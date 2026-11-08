module

/-
Finite-dimensional quadratic-form version of Lemma 3.3 (`lem:bound-gradient`):
the effective Łojasiewicz inequality.

If `spec(S) ⊆ [0,α] ∪ {1}` — which for symmetric `S` with spectrum in `[0,1]` is
equivalent to positive semidefiniteness of `(S - 1)(S - α)`, the form we take as the
hypothesis — then

    ‖grad p(ψ)‖² ≥ 16 (p(ψ) - 3α/2)(1 - p(ψ))      for unit vectors ψ.

Here `grad p(ψ) = 4 (K_ψψ - p(ψ)ψ)` (eq:acceptance grad); we take this explicit
formula as the *definition* of the gradient vector field (`gradAcc`). That it is the
actual Riemannian gradient of `accProb` on the sphere is only needed for the flow
argument (`Flow.lean`), where the chain rule `d/dt p(ψ_t) = ‖gradAcc ψ_t‖²` is proven
directly from the Fréchet derivative of `accProb`.
-/
public import GaussianTesting.GradientFlow.Moments

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {ι : Type*} [Fintype ι] {P : H2 ι →ₗ[ℂ] H2 ι}

/-- The gradient vector field of the acceptance probability on the unit sphere:
`grad p(ψ) = 4 (K_ψ ψ - p(ψ) ψ)` (eq:acceptance grad). -/
def gradAcc (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) : H ι :=
  (4 : ℂ) • (Kvec P ψ - ((accProb P ψ : ℝ) : ℂ) • ψ)

/-- `⟨ψ, K_ψ ψ⟩ = ⟨ψ⊗ψ, P ψ⊗ψ⟩` (a reshuffling of the defining sums). -/
lemma inner_psi_Kvec (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) :
    ⟪ψ, Kvec P ψ⟫_ℂ = ⟪tp2 ψ ψ, P (tp2 ψ ψ)⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Kvec_apply, tp2_apply,
    Fintype.sum_prod_type, Finset.sum_mul, map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Equation (3.5) (`eq:grad via p and q`): `‖grad p(ψ)‖² = 16 (q(ψ) - p(ψ)²)` for unit `ψ`. -/
theorem norm_gradAcc_sq (hP : IsAcceptanceProjection P) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    ‖gradAcc P ψ‖ ^ 2 = 16 * (qProb P ψ - accProb P ψ ^ 2) := by
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have hk : ⟪ψ, Kvec P ψ⟫_ℂ = (accProb P ψ : ℂ) :=
    (inner_psi_Kvec P ψ).trans (inner_tp2_P_self hP.symmetric ψ)
  have hk' : ⟪Kvec P ψ, ψ⟫_ℂ = (accProb P ψ : ℂ) := by
    rw [← inner_conj_symm, hk, Complex.conj_ofReal]
  have he : ⟪gradAcc P ψ, gradAcc P ψ⟫_ℂ =
      ((16 * (qProb P ψ - accProb P ψ ^ 2) : ℝ) : ℂ) := by
    simp only [gradAcc, inner_smul_left, inner_smul_right, inner_sub_left,
      inner_sub_right, hk, hk', hn, inner_Kvec_self, map_ofNat, Complex.conj_ofReal]
    push_cast
    ring
  have hr := congrArg Complex.re he
  change RCLike.re ⟪gradAcc P ψ, gradAcc P ψ⟫_ℂ = _ at hr
  rw [inner_self_eq_norm_sq] at hr
  simpa only [Complex.ofReal_re] using hr

/-- The spectral hypothesis `spec(S) ⊆ [0,α] ∪ {1}`, stated as positive
semidefiniteness of `(S - 1)(S - α)` (equivalent for symmetric `S` with `spec ⊆ [0,1]`). -/
def SpectralGapHyp (P : H2 ι →ₗ[ℂ] H2 ι) (α : ℝ) : Prop :=
  ∀ f : H3 ι,
    0 ≤ (⟪f, ((Sop P - LinearMap.id) ∘ₗ (Sop P - ((α : ℂ) • LinearMap.id))) f⟫_ℂ).re

/-- Second-moment lower bound: under the spectral gap hypothesis,
`q(ψ) ≥ p(ψ) - (3α/2)(1 - p(ψ))` (the rearranged display in the proof of
lem:bound-gradient). -/
theorem qProb_ge_of_gap (hP : IsAcceptanceProjection P) {α : ℝ}
    (hgap : SpectralGapHyp P α) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    accProb P ψ - 3 / 2 * α * (1 - accProb P ψ) ≤ qProb P ψ := by
  have hs : (Sop P).IsSymmetric := by
    unfold Sop
    exact ((p12_isSymmetric hP.symmetric).add (p13_isSymmetric hP.symmetric) |>.add
      (p23_isSymmetric hP.symmetric)).smul (by simp only [map_inv₀, map_ofNat])
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have ht : ⟪tp3 ψ ψ ψ, tp3 ψ ψ ψ⟫_ℂ = 1 := by
    rw [inner_tp3_tp3, hn]; simp
  have hss : ⟪tp3 ψ ψ ψ, Sop P (Sop P (tp3 ψ ψ ψ))⟫_ℂ =
      ⟪Sop P (tp3 ψ ψ ψ), Sop P (tp3 ψ ψ ψ)⟫_ℂ := (hs _ _).symm
  have hg := hgap (tp3 ψ ψ ψ)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul, inner_sub_right, inner_smul_right,
    hss, inner_tp3_Sop_tp3 hP hψ, inner_Sop_Sop_tp3 hP hψ, ht] at hg
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re] at hg
  nlinarith

/-- lem:bound-gradient: `‖grad p‖² ≥ 16 (p - 3α/2)(1 - p)`. -/
theorem norm_gradAcc_sq_ge (hP : IsAcceptanceProjection P) {α : ℝ}
    (hgap : SpectralGapHyp P α) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    16 * (accProb P ψ - 3 / 2 * α) * (1 - accProb P ψ) ≤ ‖gradAcc P ψ‖ ^ 2 := by
  rw [norm_gradAcc_sq hP hψ]
  have hq := qProb_ge_of_gap hP hgap hψ
  nlinarith

/-! ### Elementary bounds on `p` -/

/-- `p(ψ) ≥ 0` (it is `‖P ψ⊗ψ‖²`). -/
lemma accProb_nonneg (hP : IsAcceptanceProjection P) (ψ : H ι) :
    0 ≤ accProb P ψ := by
  have hi : P (P (tp2 ψ ψ)) = P (tp2 ψ ψ) :=
    LinearMap.congr_fun hP.idem (tp2 ψ ψ)
  unfold accProb
  rw [← hi, ← hP.symmetric]
  exact inner_self_nonneg (𝕜 := ℂ) (x := P (tp2 ψ ψ))

/-- `p(ψ) ≤ 1` for unit `ψ` (projections are contractions). -/
lemma accProb_le_one (hP : IsAcceptanceProjection P) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    accProb P ψ ≤ 1 := by
  let x := tp2 ψ ψ
  have hi : P (P x) = P x := LinearMap.congr_fun hP.idem x
  have hp : accProb P ψ = ‖P x‖ ^ 2 := by
    change (⟪x, P x⟫_ℂ).re = _
    rw [← hi, ← hP.symmetric, hi]
    change RCLike.re ⟪P x, P x⟫_ℂ = _
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (P x)
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have hx : ‖x‖ = 1 := by
    have hx2 : ‖x‖ ^ 2 = 1 := by
      have ht : ⟪x, x⟫_ℂ = 1 := by
        change ⟪tp2 ψ ψ, tp2 ψ ψ⟫_ℂ = 1
        rw [inner_tp2_tp2, hn, mul_one]
      have hr := congrArg (RCLike.re : ℂ → ℝ) ht
      rw [inner_self_eq_norm_sq] at hr
      exact hr
    nlinarith [norm_nonneg x]
  have hc := re_inner_le_norm (𝕜 := ℂ) (P x) x
  have he : (⟪P x, x⟫_ℂ).re = ‖P x‖ ^ 2 := by
    rw [hP.symmetric, ← hi, ← hP.symmetric, hi]
    change RCLike.re ⟪P x, P x⟫_ℂ = _
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (P x)
  change (⟪P x, x⟫_ℂ).re ≤ ‖P x‖ * ‖x‖ at hc
  rw [he, hx, mul_one] at hc
  rw [hp]
  nlinarith [norm_nonneg (P x)]

end

end GaussianTesting
