module

/-
Fidelity and angular bounds of Theorem 3.4 over arbitrary complex Hilbert
spaces, from the moment inequality used in the bosonic testing results.

The two-copy space is abstracted as a `TensorSquare`: a continuous bilinear elementary
tensor with multiplicative inner products and a swap isometry. The contraction
`K_ψψ = (I ⊗ ⟨ψ|) P ψ⊗ψ` is defined by Riesz representation, replacing
all coordinate computations by its defining property
`⟪v, contr φ y⟫ = ⟪tp v φ, y⟫`. Compactness is replaced by explicit constants
(the vector field is polynomial with `‖P‖ ≤ 1`) and completeness (the flow limit
comes from the Cauchy chord bound). The spectral input is abstracted as
`LojasiewiczData α : q(ψ) ≥ p(ψ) − (3α/2)(1−p(ψ))` — exactly what the three-copy
moment identities and the blockwise Kac gap give in the applications.
The half-angle formula for cosine gives the linear fidelity bound for the same
certainty-state witness. `SharpRobustness.lean` states both conclusions with one
witness at every error level under this moment hypothesis. `HilbertGradientBound.lean`
derives the moment inequality from the spectrum on the completed three-copy space.
`HilbertSpectralGap.lean` proves the spectral theorem using the projective flow
and its certainty limit.

As in the finite-dimensional argument, the proof bounds the distance along
the flow using the scalar potential `Vpot`. On every subinterval, the chord
length is at most the decrease in this potential. Summing over partitions
bounds the projective angle, and continuity gives the bound at the limit.
Here the Riesz characterization
replaces finite coordinate sums, and explicit bounds give a uniform time
interval for local solutions.
-/
public import GaussianTesting.GradientFlow.Robustness
public import GaussianTesting.GradientFlow.Angle
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace
open Set

noncomputable section

/-- An abstract two-copy structure on a Hilbert space `H`: a continuous bilinear
elementary tensor into `K` with multiplicative inner products, and a swap isometry
exchanging the factors. Instances: the finite product-index model (`tp2`), and
`ℓ²(ι) × ℓ²(ι) → ℓ²(ι × ι)` for the bosonic Fock space. -/
structure TensorSquare (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] where
  tp : H →L[ℂ] H →L[ℂ] K
  inner_tp : ∀ a b c d : H, ⟪tp a b, tp c d⟫_ℂ = ⟪a, c⟫_ℂ * ⟪b, d⟫_ℂ
  swap : K ≃ₗᵢ[ℂ] K
  swap_tp : ∀ a b : H, swap (tp a b) = tp b a

variable {H K : Type*} [NormedAddCommGroup H] [innerH : InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [completeH : CompleteSpace H] [completeK : CompleteSpace K]

namespace TensorSquare

variable (T : TensorSquare H K)

omit completeH completeK in
lemma norm_tp [CompleteSpace H] [CompleteSpace K] (T : TensorSquare H K) (a b : H) : ‖T.tp a b‖ = ‖a‖ * ‖b‖ := by
  have h := congrArg Complex.re (T.inner_tp a b a b)
  simp only [inner_self_eq_norm_sq_to_K] at h
  change ((‖T.tp a b‖ : ℂ) ^ 2).re = ((‖a‖ : ℂ) ^ 2 * (‖b‖ : ℂ) ^ 2).re at h
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul] at h
  nlinarith [norm_nonneg (T.tp a b), mul_nonneg (norm_nonneg a) (norm_nonneg b)]

/-- An acceptance projection: self-adjoint idempotent commuting with the swap. -/
structure IsAcceptance (P : K →L[ℂ] K) : Prop where
  symmetric : ∀ x y : K, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ
  idem : P ∘L P = P
  swap_comm : ∀ x : K, P (T.swap x) = T.swap (P x)

omit [CompleteSpace H] in
/-- A symmetric idempotent acceptance operator is a contraction. -/
theorem IsAcceptance.norm_le_one {T : TensorSquare H K} {P : K →L[ℂ] K} (hP : T.IsAcceptance P) : ‖P‖ ≤ 1 :=
  IsStarProjection.norm_le P ⟨hP.idem, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hP.symmetric⟩

variable (P : K →L[ℂ] K)

/-- Acceptance probability `p(ψ)`. -/
def accProbA (ψ : H) : ℝ := (⟪T.tp ψ ψ, P (T.tp ψ ψ)⟫_ℂ).re

/-- The contraction `(φ, y) ↦ (I ⊗ ⟨φ|) y`, defined by Riesz representation:
the unique vector with `⟪v, contr φ y⟫ = ⟪tp v φ, y⟫` for all `v`. -/
def contr (φ : H) (y : K) : H :=
  (InnerProductSpace.toDual ℂ H).symm
    ((innerSL ℂ y).comp ((T.tp.flip) φ))

omit completeK in
/-- Defining property of the contraction. -/
lemma inner_contr [CompleteSpace K] (T : TensorSquare H K) (φ : H) (y : K) (v : H) :
    ⟪v, T.contr φ y⟫_ℂ = ⟪T.tp v φ, y⟫_ℂ := by
  rw [← inner_conj_symm, ← inner_conj_symm (T.tp v φ) y]
  congr 1
  exact InnerProductSpace.toDual_symm_apply

lemma norm_contr_le (φ : H) (y : K) : ‖T.contr φ y‖ ≤ ‖φ‖ * ‖y‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (T.tp (T.contr φ y) φ) y
  rw [← T.inner_contr, inner_self_eq_norm_sq_to_K, T.norm_tp] at h
  change ‖(‖T.contr φ y‖ : ℂ) ^ 2‖ ≤ _ at h
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] at h
  by_cases hz : ‖T.contr φ y‖ = 0
  · rw [hz]; positivity
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp
    nlinarith only [h]

/-- `K_ψψ`. -/
def KvecA (ψ : H) : H := T.contr ψ (P (T.tp ψ ψ))

/-- `q(ψ) = ‖K_ψψ‖²`. -/
def qProbA (ψ : H) : ℝ := ‖T.KvecA P ψ‖ ^ 2

/-- The gradient vector field `4(K_ψψ − p(ψ)ψ)`. -/
def gradAccA (ψ : H) : H := (4 : ℂ) • (T.KvecA P ψ - ((T.accProbA P ψ : ℝ) : ℂ) • ψ)

/-- The abstract spectral input: the Łojasiewicz data produced by the three-copy
moment identities and a spectral gap `spec(S) ⊆ [0,α] ∪ {1}` (cf. Lemmas 3.2 + 3.3). -/
def LojasiewiczData (α : ℝ) : Prop :=
  ∀ ψ : H, ‖ψ‖ = 1 →
    T.accProbA P ψ - 3 / 2 * α * (1 - T.accProbA P ψ) ≤ T.qProbA P ψ

variable {P}

/-! ### Acceptance, contraction, and gradient identities -/

lemma inner_psi_KvecA (ψ : H) :
    ⟪ψ, T.KvecA P ψ⟫_ℂ = ⟪T.tp ψ ψ, P (T.tp ψ ψ)⟫_ℂ := by
  exact T.inner_contr ψ (P (T.tp ψ ψ)) ψ

omit completeH completeK in
lemma inner_tp_P_self [CompleteSpace H] [CompleteSpace K] (T : TensorSquare H K) {P : K →L[ℂ] K} (hP : T.IsAcceptance P) (ψ : H) :
    ⟪T.tp ψ ψ, P (T.tp ψ ψ)⟫_ℂ = ((T.accProbA P ψ : ℝ) : ℂ) := by
  unfold accProbA
  apply Eq.symm
  apply Complex.conj_eq_iff_re.mp
  rw [inner_conj_symm]
  exact hP.symmetric _ _

omit completeH completeK in
lemma accProbA_nonneg [CompleteSpace H] [CompleteSpace K] (T : TensorSquare H K) {P : K →L[ℂ] K} (hP : T.IsAcceptance P) (ψ : H) : 0 ≤ T.accProbA P ψ := by
  have hi : P (P (T.tp ψ ψ)) = P (T.tp ψ ψ) :=
    DFunLike.congr_fun hP.idem (T.tp ψ ψ)
  unfold accProbA
  rw [← hi, ← hP.symmetric]
  exact inner_self_nonneg (𝕜 := ℂ) (x := P (T.tp ψ ψ))

omit completeH completeK in
lemma accProbA_le_one [CompleteSpace H] [CompleteSpace K] (T : TensorSquare H K) {P : K →L[ℂ] K} (hP : T.IsAcceptance P) {ψ : H} (hψ : ‖ψ‖ = 1) :
    T.accProbA P ψ ≤ 1 := by
  let x := T.tp ψ ψ
  have hi : P (P x) = P x := DFunLike.congr_fun hP.idem x
  have hp : T.accProbA P ψ = ‖P x‖ ^ 2 := by
    change (⟪x, P x⟫_ℂ).re = _
    rw [← hi, ← hP.symmetric, hi]
    change RCLike.re ⟪P x, P x⟫_ℂ = _
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (P x)
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have hx : ‖x‖ = 1 := by
    have hx2 : ‖x‖ ^ 2 = 1 := by
      have ht : ⟪x, x⟫_ℂ = 1 := by
        change ⟪T.tp ψ ψ, T.tp ψ ψ⟫_ℂ = 1
        rw [T.inner_tp, hn, mul_one]
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

lemma qProbA_le_accProbA (hP : T.IsAcceptance P) {ψ : H} (hψ : ‖ψ‖ = 1) :
    T.qProbA P ψ ≤ T.accProbA P ψ := by
  have hi : P (P (T.tp ψ ψ)) = P (T.tp ψ ψ) :=
    DFunLike.congr_fun hP.idem (T.tp ψ ψ)
  have hp : T.accProbA P ψ = ‖P (T.tp ψ ψ)‖ ^ 2 := by
    unfold accProbA
    rw [← hi, ← hP.symmetric, hi]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h := T.norm_contr_le ψ (P (T.tp ψ ψ))
  change ‖T.KvecA P ψ‖ ≤ ‖ψ‖ * _ at h
  rw [hψ, one_mul] at h
  unfold qProbA
  rw [hp]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem norm_gradAccA_sq (hP : T.IsAcceptance P) {ψ : H} (hψ : ‖ψ‖ = 1) :
    ‖T.gradAccA P ψ‖ ^ 2 = 16 * (T.qProbA P ψ - T.accProbA P ψ ^ 2) := by
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have hk : ⟪ψ, T.KvecA P ψ⟫_ℂ = (T.accProbA P ψ : ℂ) :=
    (T.inner_psi_KvecA ψ).trans (T.inner_tp_P_self hP ψ)
  have hk' : ⟪T.KvecA P ψ, ψ⟫_ℂ = (T.accProbA P ψ : ℂ) := by
    rw [← inner_conj_symm, hk, Complex.conj_ofReal]
  have hkk : ⟪T.KvecA P ψ, T.KvecA P ψ⟫_ℂ = (T.qProbA P ψ : ℂ) := by
    simp [qProbA, inner_self_eq_norm_sq_to_K]
  have he : ⟪T.gradAccA P ψ, T.gradAccA P ψ⟫_ℂ =
      ((16 * (T.qProbA P ψ - T.accProbA P ψ ^ 2) : ℝ) : ℂ) := by
    simp only [gradAccA, inner_smul_left, inner_smul_right, inner_sub_left,
      inner_sub_right, hk, hk', hn, hkk, map_ofNat, Complex.conj_ofReal]
    unfold qProbA
    push_cast
    ring
  have hr := congrArg Complex.re he
  change RCLike.re ⟪T.gradAccA P ψ, T.gradAccA P ψ⟫_ℂ = _ at hr
  rw [inner_self_eq_norm_sq] at hr
  simpa only [Complex.ofReal_re] using hr

private lemma bilinear_tp_private :
    IsBoundedBilinearMap ℂ (fun p : H × H => T.tp p.1 p.2) := by
  refine ⟨?_, ?_, ?_, ?_, 1, by norm_num, ?_⟩
  · intro x z y; simp
  · intro c x y; simp
  · intro x y z; simp
  · intro c x y; simp
  · intro x y; simp [T.norm_tp]

private lemma smooth_tp_private : ContDiff ℝ (⊤ : ℕ∞) (fun ψ : H => T.tp ψ ψ) := by
  exact (show ContDiff ℂ (⊤ : ℕ∞) (fun ψ : H => T.tp ψ ψ) from
    (bilinear_tp_private T).contDiff.comp (contDiff_id.prodMk contDiff_id)).restrict_scalars ℝ

private lemma smooth_acc_private : ContDiff ℝ (⊤ : ℕ∞) (T.accProbA P) := by
  exact Complex.reCLM.contDiff.comp
    ((smooth_tp_private T).inner ℂ ((P.restrictScalars ℝ).contDiff.comp (smooth_tp_private T)))

theorem hasFDerivAt_accProbA (hP : T.IsAcceptance P) (ψ : H) :
    HasFDerivAt (T.accProbA P)
      ((4 : ℝ) • (Complex.reCLM.comp
        (((innerSL ℂ) (T.KvecA P ψ)).restrictScalars ℝ))) ψ := by
  let D := (bilinear_tp_private T).deriv (ψ, ψ) |>.comp
    ((ContinuousLinearMap.id ℂ (H)).prod (ContinuousLinearMap.id ℂ (H)))
  have ht : HasFDerivAt (fun x : H => T.tp x x) (D.restrictScalars ℝ) ψ := by
    have hd : HasFDerivAt (fun x : H => (x, x))
        ((ContinuousLinearMap.id ℂ (H)).prod (ContinuousLinearMap.id ℂ (H))) ψ :=
      (hasFDerivAt_id ψ).prodMk (hasFDerivAt_id ψ)
    exact (HasFDerivAt.comp (f := fun x : H => (x, x)) ψ
      ((bilinear_tp_private T).hasFDerivAt (ψ, ψ)) hd).restrictScalars ℝ
  have hp := (P.restrictScalars ℝ).hasFDerivAt.comp ψ ht
  have h := Complex.reCLM.hasFDerivAt.comp ψ (ht.inner ℂ hp)
  change HasFDerivAt (T.accProbA P) _ ψ at h
  apply h.congr_fderiv
  ext v
  change (⟪T.tp ψ ψ, P (T.tp ψ v + T.tp v ψ)⟫_ℂ +
    ⟪T.tp ψ v + T.tp v ψ, P (T.tp ψ ψ)⟫_ℂ).re = 4 * (⟪T.KvecA P ψ, v⟫_ℂ).re
  have hs : ⟪T.tp ψ v, P (T.tp ψ ψ)⟫_ℂ = ⟪v, T.KvecA P ψ⟫_ℂ := by
    have he : ⟪T.tp ψ v, P (T.tp ψ ψ)⟫_ℂ =
        ⟪T.tp v ψ, P (T.tp ψ ψ)⟫_ℂ := by
      have hy : T.swap (P (T.tp ψ ψ)) = P (T.tp ψ ψ) := by
        rw [← hP.swap_comm, T.swap_tp]
      rw [← T.swap_tp v ψ]
      calc
        _ = ⟪T.swap (T.tp v ψ), T.swap (P (T.tp ψ ψ))⟫_ℂ := by rw [hy]
        _ = _ := T.swap.inner_map_map _ _
    rw [he, ← T.inner_contr]
    rfl
  have ha : ⟪T.tp v ψ, P (T.tp ψ ψ)⟫_ℂ = ⟪v, T.KvecA P ψ⟫_ℂ := by
    exact (T.inner_contr ψ (P (T.tp ψ ψ)) v).symm
  have hb : ⟪T.tp ψ ψ, P (T.tp ψ v + T.tp v ψ)⟫_ℂ =
      (starRingEnd ℂ) ⟪T.tp ψ v + T.tp v ψ, P (T.tp ψ ψ)⟫_ℂ := by
    rw [inner_conj_symm, hP.symmetric]
  rw [hb, inner_add_left, hs, ha]
  have hr : (⟪v, T.KvecA P ψ⟫_ℂ).re = (⟪T.KvecA P ψ, v⟫_ℂ).re := by
    rw [← inner_conj_symm v (T.KvecA P ψ), Complex.conj_re]
  simp only [Complex.add_re, Complex.conj_re, hr]
  ring

lemma re_inner_gradAccA (hP : T.IsAcceptance P) (ψ : H) :
    (⟪ψ, T.gradAccA P ψ⟫_ℂ).re = 4 * T.accProbA P ψ * (1 - ‖ψ‖ ^ 2) := by
  have hk : ⟪ψ, T.KvecA P ψ⟫_ℂ = (T.accProbA P ψ : ℂ) :=
    (T.inner_psi_KvecA ψ).trans (T.inner_tp_P_self hP ψ)
  simp only [gradAccA, inner_smul_right, inner_sub_right, hk,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  ring

private lemma bilinear_contr_private :
    IsBoundedBilinearMap ℝ (fun p : H × K => T.contr p.1 p.2) := by
  refine ⟨?_, ?_, ?_, ?_, 1, by norm_num, ?_⟩
  · intro x z y
    apply ext_inner_left ℂ
    intro v
    simp [T.inner_contr, map_add, inner_add_left, inner_add_right]
  · intro c x y
    apply ext_inner_left ℂ
    intro v
    simp [T.inner_contr, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  · intro x y z
    apply ext_inner_left ℂ
    intro v
    simp [T.inner_contr, inner_add_right]
  · intro c x y
    apply ext_inner_left ℂ
    intro v
    simp [T.inner_contr, inner_smul_right_eq_smul]
  · intro x y; simpa using T.norm_contr_le x y

/-- The vector field in Eq. (3.4) is smooth over the reals on the entire
Hilbert space, for every bounded two-copy operator. -/
theorem contDiff_gradAccA (P : K →L[ℂ] K) : ContDiff ℝ (⊤ : ℕ∞) (T.gradAccA P) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun x : H => T.tp x x) :=
    (show ContDiff ℂ (⊤ : ℕ∞) (fun x : H => T.tp x x) from
      T.tp.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).restrict_scalars ℝ
  have hPtp : ContDiff ℝ (⊤ : ℕ∞) (fun x : H => P (T.tp x x)) :=
    (P.restrictScalars ℝ).contDiff.comp ht
  have hp : ContDiff ℝ (⊤ : ℕ∞) (T.accProbA P) := Complex.reCLM.contDiff.comp (ht.inner ℂ hPtp)
  have hK : ContDiff ℝ (⊤ : ℕ∞) (T.KvecA P) :=
    (bilinear_contr_private T).contDiff.comp (contDiff_id.prodMk hPtp)
  exact (hK.sub ((Complex.ofRealCLM.contDiff.comp hp).smul contDiff_id)).const_smul (4 : ℂ)

omit innerH completeH in
private lemma bilip_bound_private [InnerProductSpace ℂ H] [CompleteSpace H] {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {b : E × F → G} (hb : IsBoundedBilinearMap 𝕜 b)
    {s : Set H} {f : H → E} {g : H → F}
    (bf : ∃ A : ℝ, ∀ x ∈ s, ‖f x‖ ≤ A)
    (bg : ∃ B : ℝ, ∀ x ∈ s, ‖g x‖ ≤ B)
    (lf : ∃ A, LipschitzOnWith A f s) (lg : ∃ B, LipschitzOnWith B g s) :
    (∃ C : ℝ, ∀ x ∈ s, ‖b (f x, g x)‖ ≤ C) ∧
    ∃ C, LipschitzOnWith C (fun x => b (f x, g x)) s := by
  obtain ⟨A, hA⟩ := bf
  obtain ⟨B, hB⟩ := bg
  obtain ⟨Kf, hf⟩ := lf
  obtain ⟨Kg, hg⟩ := lg
  obtain ⟨C, hC, hc⟩ := hb.bound
  constructor
  · refine ⟨C * max A 0 * max B 0, ?_⟩
    intro x hx
    exact (hc _ _).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left ((hA x hx).trans (le_max_left _ _)) hC.le)
      ((hB x hx).trans (le_max_left _ _)) (norm_nonneg _) (by positivity))
  · let L := C * (max A 0 * (Kg : ℝ) + max B 0 * (Kf : ℝ))
    have hL : 0 ≤ L := by dsimp [L]; positivity
    refine ⟨Real.toNNReal L, ?_⟩
    rw [lipschitzOnWith_iff_norm_sub_le] at hf hg ⊢
    intro x hx y hy
    rw [Real.coe_toNNReal _ hL]
    have he : b (f x, g x) - b (f y, g y) =
        b (f x, g x - g y) + b (f x - f y, g y) := by
      rw [hb.map_sub_left, hb.map_sub_right]; abel
    rw [he]
    calc
      _ ≤ ‖b (f x, g x - g y)‖ + ‖b (f x - f y, g y)‖ := norm_add_le _ _
      _ ≤ C * ‖f x‖ * ‖g x - g y‖ + C * ‖f x - f y‖ * ‖g y‖ :=
        add_le_add (hc _ _) (hc _ _)
      _ ≤ C * (max A 0) * ((Kg : ℝ) * ‖x - y‖) +
          C * ((Kf : ℝ) * ‖x - y‖) * (max B 0) := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left ((hA x hx).trans (le_max_left _ _))
            hC.le) (hg hx hy) (norm_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (hf hx hy) hC.le)
            ((hB y hy).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ = L * ‖x - y‖ := by dsimp [L]; ring

/-- Explicit Lipschitz bound on `closedBall 0 2` (no compactness). -/
theorem lipschitzOnWith_gradAccA (_hP : T.IsAcceptance P) (_hPnorm : ‖P‖ ≤ 1) :
    ∃ L : NNReal, LipschitzOnWith L (T.gradAccA P) (Metric.closedBall 0 2) := by
  let s := Metric.closedBall (0 : H) 2
  have bid : ∃ A : ℝ, ∀ x ∈ s, ‖x‖ ≤ A := ⟨2, by
    intro x hx; simpa [s, Metric.mem_closedBall, dist_eq_norm] using hx⟩
  have btp : IsBoundedBilinearMap ℝ (fun p : H × H => T.tp p.1 p.2) := by
    refine ⟨?_, ?_, ?_, ?_, 1, by norm_num, ?_⟩
    · intro x z y; simp
    · intro c x y; simp
    · intro x y z; simp
    · intro c x y; simp
    · intro x y; simp [T.norm_tp]
  have lid : ∃ A, LipschitzOnWith A (id : H → H) s :=
    ⟨1, LipschitzWith.id.lipschitzOnWith⟩
  obtain ⟨bt, Kt, ht⟩ := bilip_bound_private
    btp bid bid lid lid
  have by' : ∃ B : ℝ, ∀ x ∈ s, ‖P (T.tp x x)‖ ≤ B := by
    obtain ⟨A, hA⟩ := bt
    exact ⟨‖P‖ * max A 0, fun x hx => (P.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hA x hx).trans (le_max_left _ _)) (norm_nonneg _))⟩
  have ly : ∃ A, LipschitzOnWith A (fun x => P (T.tp x x)) s :=
    ⟨_, P.lipschitzWith.comp_lipschitzOnWith ht⟩
  obtain ⟨bk, Kk, hk⟩ := bilip_bound_private (bilinear_contr_private T) bid by' lid ly
  obtain ⟨bi, Ki, hi⟩ := bilip_bound_private
    (isBoundedBilinearMap_inner (𝕜 := ℂ) (E := K)) bt by' ⟨Kt, ht⟩ ly
  have bp : ∃ A : ℝ, ∀ x ∈ s, ‖(T.accProbA P x : ℂ)‖ ≤ A := by
    obtain ⟨A, hA⟩ := bi
    refine ⟨A, fun x hx => ?_⟩
    have hh : ‖(T.accProbA P x : ℂ)‖ ≤ ‖⟪T.tp x x, P (T.tp x x)⟫_ℂ‖ := by
      simpa [accProbA] using Complex.abs_re_le_norm ⟪T.tp x x, P (T.tp x x)⟫_ℂ
    exact hh.trans (hA x hx)
  have lp : ∃ A, LipschitzOnWith A (fun x => (T.accProbA P x : ℂ)) s :=
    ⟨_, Complex.ofRealCLM.lipschitzWith.comp_lipschitzOnWith
      (Complex.reCLM.lipschitzWith.comp_lipschitzOnWith hi)⟩
  obtain ⟨bm, Km, hm⟩ := bilip_bound_private
    (isBoundedBilinearMap_smul (𝕜 := ℂ) (E := H)) bp bid lp lid
  exact ⟨_, (((4 : ℂ) • ContinuousLinearMap.id ℂ H).lipschitzWith.comp_lipschitzOnWith
    (hk.sub hm))⟩

theorem norm_gradAccA_le (_hP : T.IsAcceptance P) (hPnorm : ‖P‖ ≤ 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ Metric.closedBall (0 : H) 2, ‖T.gradAccA P ψ‖ ≤ M := by
  refine ⟨160, by norm_num, ?_⟩
  intro ψ hψ
  have hn : ‖ψ‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hψ
  have ht : ‖T.tp ψ ψ‖ ≤ 4 := by rw [T.norm_tp]; nlinarith [norm_nonneg ψ]
  have hy : ‖P (T.tp ψ ψ)‖ ≤ 4 := (P.le_opNorm _).trans
    (by nlinarith [norm_nonneg (T.tp ψ ψ)])
  have hk : ‖T.KvecA P ψ‖ ≤ 8 := (T.norm_contr_le _ _).trans
    (by nlinarith [norm_nonneg ψ, norm_nonneg (P (T.tp ψ ψ))])
  have hp : |T.accProbA P ψ| ≤ 16 :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (by nlinarith [norm_nonneg (T.tp ψ ψ), norm_nonneg (P (T.tp ψ ψ))]))
  calc
    ‖T.gradAccA P ψ‖ = 4 * ‖T.KvecA P ψ - (T.accProbA P ψ : ℂ) • ψ‖ := by
      simp [gradAccA, norm_smul]
    _ ≤ 4 * (‖T.KvecA P ψ‖ + |T.accProbA P ψ| * ‖ψ‖) := by
      exact mul_le_mul_of_nonneg_left (by simpa [norm_smul] using
        (norm_sub_le (T.KvecA P ψ) ((T.accProbA P ψ : ℂ) • ψ))) (by norm_num)
    _ ≤ 160 := by nlinarith [abs_nonneg (T.accProbA P ψ)]

/-- A unit-vector solution of Eq. (3.4) on a time domain. The derivative is taken
within the domain, so the endpoints of a closed interval have one-sided derivatives. -/
structure IsUnitFlowOn (P : K →L[ℂ] K) (γ : ℝ → H) (s : Set ℝ) : Prop where
  sphere : ∀ t ∈ s, ‖γ t‖ = 1
  deriv : ∀ t ∈ s, HasDerivWithinAt γ (T.gradAccA P (γ t)) s t

omit [CompleteSpace K] in
/-- Restriction of a unit-vector solution to a smaller time domain. -/
theorem IsUnitFlowOn.mono {T : TensorSquare H K} {γ : ℝ → H} {s u : Set ℝ}
    (hγ : T.IsUnitFlowOn P γ s) (hu : u ⊆ s) : T.IsUnitFlowOn P γ u :=
  ⟨fun t ht => hγ.sphere t (hu ht), fun t ht => (hγ.deriv t (hu ht)).mono hu⟩

/-- Any local solution is smooth in time on its closed interval, including the endpoints. -/
theorem IsUnitFlowOn.contDiffOn {T : TensorSquare H K} {γ : ℝ → H} {a b : ℝ}
    (hγ : T.IsUnitFlowOn P γ (Icc a b)) : ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc a b) := by
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (f := fun _ x => T.gradAccA P x) (u := univ)
  · exact ((T.contDiff_gradAccA P).comp
      (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (Prod.snd : ℝ × H → H))).contDiffOn
  · exact hγ.deriv
  · exact fun _ _ => mem_univ _

private structure SegA (P : K →L[ℂ] K) (δ : ℝ) (x₀ : H) (γ : ℝ → H) : Prop
    extends T.IsUnitFlowOn P γ (Icc 0 δ) where
  init : γ 0 = x₀

/-- Uniform-step local existence: there is a single `δ > 0` (depending only on `P`)
such that from every initial point on the unit sphere the flow exists on `[0, δ]` and
stays on the sphere. (Picard–Lindelöf with the Lipschitz data of
`lipschitzOnWith_gradAccA`/`norm_gradAccA_le` on `closedBall 0 2`, plus sphere invariance
via a Grönwall estimate for `‖γ t‖² - 1`, whose derivative is `8p(γ)(1 - ‖γ‖²)` by
`T.re_inner_gradAccA`.) -/
private theorem exists_seg_private (hP : T.IsAcceptance P) (hPnorm : ‖P‖ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ : H, ‖x₀‖ = 1 → ∃ γ, SegA T P δ x₀ γ := by
  obtain ⟨K, hK⟩ := T.lipschitzOnWith_gradAccA hP hPnorm
  obtain ⟨M, hM0, hM⟩ := T.norm_gradAccA_le hP hPnorm
  let δ : ℝ := 1 / M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀
  have hball : Metric.closedBall x₀ 1 ⊆ Metric.closedBall (0 : H) 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx ⊢
    have hh := norm_add_le (x - x₀) x₀
    simp only [sub_add_cancel, sub_zero, hx₀] at hh ⊢
    linarith
  have hpl : IsPicardLindelof (fun _ x => T.gradAccA P x)
      (⟨0, by exact ⟨le_rfl, hδ.le⟩⟩ : Icc (0 : ℝ) δ) x₀ 1 0 ⟨M, hM0.le⟩ K := by
    constructor
    · exact fun _ _ => hK.mono hball
    · exact fun _ _ => continuousOn_const
    · exact fun _ _ x hx => hM x (hball hx)
    · change M * max (δ - 0) (0 - 0) ≤ (1 : ℝ) - 0
      simp only [sub_zero, sub_self, max_eq_left hδ.le]
      dsimp [δ]
      rw [mul_one_div_cancel hM0.ne']
  obtain ⟨γ, hγ0, hγd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hcont : ContinuousOn γ (Icc 0 δ) := fun t ht => (hγd t ht).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((smooth_acc_private T (P := P)).continuous.comp_continuousOn hcont)
  let e : ℝ → ℝ := fun t => ‖γ t‖ ^ 2 - 1
  have he (t : ℝ) (ht : t ∈ Icc 0 δ) :
      HasDerivWithinAt e (-(8 * T.accProbA P (γ t)) * e t) (Icc 0 δ) t := by
    have hi := (hγd t ht).inner ℂ (hγd t ht)
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hi
    have hd := hr.sub_const 1
    have hfun : (fun s => (⟪γ s, γ s⟫_ℂ).re - 1) = e := by
      funext s
      exact congrArg (fun x : ℝ => x - 1) (inner_self_eq_norm_sq (𝕜 := ℂ) (γ s))
    change HasDerivWithinAt (fun s => (⟪γ s, γ s⟫_ℂ).re - 1)
      ((⟪γ t, T.gradAccA P (γ t)⟫_ℂ + ⟪T.gradAccA P (γ t), γ t⟫_ℂ).re) _ t at hd
    rw [hfun] at hd
    convert hd using 1
    simp only [Complex.add_re]
    rw [show (⟪T.gradAccA P (γ t), γ t⟫_ℂ).re =
      (⟪γ t, T.gradAccA P (γ t)⟫_ℂ).re from inner_re_symm (𝕜 := ℂ) _ _,
      T.re_inner_gradAccA hP]
    dsimp [e]; ring
  have he0 : e 0 = 0 := by simp [e, hγ0, hx₀]
  have hezero : ∀ t ∈ Icc 0 δ, e t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (fun t ht => (he t ht).continuousWithinAt)
      (f' := fun t => -(8 * T.accProbA P (γ t)) * e t) (K := 8 * C) ?_ he0 ?_
    · intro t ht
      exact ((he t ⟨ht.1, ht.2.le⟩).mono
        (show Icc t δ ⊆ Icc 0 δ from fun s hs => ⟨ht.1.trans hs.1, hs.2⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE ht.2)
    · intro t ht
      have hb := hC t ⟨ht.1, ht.2.le⟩
      simp only [Real.norm_eq_abs] at hb ⊢
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num))
        (abs_nonneg _)
  refine ⟨γ, ⟨⟨?_, hγd⟩, hγ0⟩⟩
  intro t ht
  have hz := hezero t ht
  dsimp [e] at hz
  nlinarith [norm_nonneg (γ t)]

/-- From each unit initial vector a smooth unit-vector solution exists on a
positive time interval, using only local Picard–Lindelöf existence and sphere invariance. -/
theorem exists_smooth_local_unitFlow (hP : T.IsAcceptance P) :
    ∃ δ > (0 : ℝ), ∀ x₀ : H, ‖x₀‖ = 1 → ∃ γ : ℝ → H,
      γ 0 = x₀ ∧ T.IsUnitFlowOn P γ (Icc 0 δ) ∧ ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 δ) := by
  obtain ⟨δ, hδ, hseg⟩ := exists_seg_private T hP hP.norm_le_one
  refine ⟨δ, hδ, fun x₀ hx₀ => ?_⟩
  obtain ⟨γ, hγ⟩ := hseg x₀ hx₀
  exact ⟨γ, hγ.init, hγ.toIsUnitFlowOn, hγ.toIsUnitFlowOn.contDiffOn⟩

/-! ### B. The global flow -/


/-- Global flow on `[0, ∞)`. Uniform Lipschitz and norm bounds give local
Picard–Lindelöf solutions on intervals of the same length. A Grönwall estimate
keeps each solution on the unit sphere, so the intervals can be joined. -/
theorem exists_global_flowA (hP : T.IsAcceptance P) (hPnorm : ‖P‖ ≤ 1)
    {x₀ : H} (hx₀ : ‖x₀‖ = 1) :
    ∃ γ : ℝ → H, γ 0 = x₀ ∧ (∀ t ∈ Ici (0 : ℝ), ‖γ t‖ = 1) ∧
      ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt γ (T.gradAccA P (γ t)) (Ici 0) t := by
  classical
  obtain ⟨δ, hδ, hseg⟩ := exists_seg_private T hP hPnorm
  let X : ℕ → {x : H // ‖x‖ = 1} := Nat.rec ⟨x₀, hx₀⟩
    (fun _ x => ⟨Classical.choose (hseg x.1 x.2) δ,
      (Classical.choose_spec (hseg x.1 x.2)).sphere δ ⟨hδ.le, le_rfl⟩⟩)
  let c : ℕ → ℝ → H := fun n => Classical.choose (hseg (X n).1 (X n).2)
  have hc (n : ℕ) : SegA T P δ (X n).1 (c n) := Classical.choose_spec _
  have hnext (n : ℕ) : (X (n + 1)).1 = c n δ := rfl
  let γ : ℝ → H := fun t => c ⌊t / δ⌋₊ (t - (⌊t / δ⌋₊ : ℝ) * δ)
  have hfloor (n : ℕ) (t : ℝ) (hl : (n : ℝ) * δ ≤ t)
      (hr : t < ((n : ℝ) + 1) * δ) : ⌊t / δ⌋₊ = n := by
    apply (Nat.floor_eq_iff (div_nonneg (le_trans (by positivity : 0 ≤ (n : ℝ) * δ) hl) hδ.le)).mpr
    exact ⟨(le_div_iff₀ hδ).mpr hl, (div_lt_iff₀ hδ).mpr hr⟩
  have hcoh (n : ℕ) (t : ℝ) (ht : t ∈ Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) :
      γ t = c n (t - (n : ℝ) * δ) := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · simp [γ, hfloor n t ht.1 hlt]
    · have hf : ⌊t / δ⌋₊ = n + 1 := by
        rw [heq, mul_div_cancel_right₀ _ hδ.ne']
        simpa using (Nat.floor_natCast (n + 1) : ⌊((n + 1 : ℕ) : ℝ)⌋₊ = n + 1)
      rw [show γ t = c (n + 1) 0 by
        dsimp [γ]
        rw [hf]
        simp [heq, Nat.cast_add, Nat.cast_one]]
      rw [(hc (n + 1)).init, hnext]
      congr 1
      linarith
  have hbounds (t : ℝ) (ht : 0 ≤ t) :
      (⌊t / δ⌋₊ : ℝ) * δ ≤ t ∧ t < ((⌊t / δ⌋₊ : ℝ) + 1) * δ :=
    ⟨(le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg ht hδ.le)),
      (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (t / δ))⟩
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) :
      HasDerivWithinAt γ (T.gradAccA P (γ t))
        (Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) t := by
    have hm : MapsTo (fun s : ℝ => s - (n : ℝ) * δ)
        (Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) (Icc 0 δ) := by
      intro s hs; constructor <;> linarith [hs.1, hs.2]
    have hh := ((hc n).deriv _ (hm ht)).scomp t
      ((hasDerivWithinAt_id t _).sub_const ((n : ℝ) * δ)) hm
    simp only [one_smul, Function.comp_def] at hh
    rw [← hcoh n t ht] at hh
    exact hh.congr (fun s hs => hcoh n s hs) (hcoh n t ht)
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [show γ 0 = c 0 0 by simp [γ]]
    exact (hc 0).init
  · intro t ht
    have hb := hbounds t ht
    rw [hcoh _ t ⟨hb.1, hb.2.le⟩]
    apply (hc _).sphere
    constructor <;> linarith [hb.1, hb.2]
  · intro t ht
    let n := ⌊t / δ⌋₊
    have hb : (n : ℝ) * δ ≤ t ∧ t < ((n : ℝ) + 1) * δ := hbounds t ht
    have hdright := hd n t ⟨hb.1, hb.2.le⟩
    rcases eq_or_lt_of_le hb.1 with heq | hlt
    · cases hn : n with
      | zero =>
        have ht0 : t = 0 := by simpa [hn] using heq.symm
        rw [hn, ht0] at hdright
        rw [ht0]
        exact hdright.mono_of_mem_nhdsWithin (by simpa using Icc_mem_nhdsGE hδ)
      | succ m =>
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by simp
        rw [hn, hcast] at heq hdright hb
        have hdleft := hd m t (by constructor <;> nlinarith [hδ])
        have hu := hdleft.union hdright
        rw [Icc_union_Icc_eq_Icc (by nlinarith [hδ] : (m : ℝ) * δ ≤ ((m : ℝ) + 1) * δ)
          (by nlinarith [hδ] : ((m : ℝ) + 1) * δ ≤ ((m : ℝ) + 1 + 1) * δ)] at hu
        exact hu.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
          (Icc_mem_nhds (by nlinarith [hδ]) (by nlinarith [hδ])))
    · exact hdright.mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hlt hb.2))

variable {T}

/-- Evaluating the differential of acceptance on the unit-sphere gradient gives its squared norm. -/
theorem deriv_accProbA_gradAccA (hP : T.IsAcceptance P) {ψ : H}
    (hψ : ‖ψ‖ = 1) :
    4 * (⟪T.KvecA P ψ, T.gradAccA P ψ⟫_ℂ).re = ‖T.gradAccA P ψ‖ ^ 2 := by
  have hk : ⟪T.KvecA P ψ, ψ⟫_ℂ = (T.accProbA P ψ : ℂ) := by
    rw [← inner_conj_symm, T.inner_psi_KvecA, T.inner_tp_P_self hP,
      Complex.conj_ofReal]
  have hkk : ⟪T.KvecA P ψ, T.KvecA P ψ⟫_ℂ = (T.qProbA P ψ : ℂ) := by
    simp [qProbA, inner_self_eq_norm_sq_to_K]
  rw [T.norm_gradAccA_sq hP hψ]
  simp only [gradAccA, inner_smul_right, inner_sub_right, hkk, hk]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

private lemma norm_gradAccA_sq_ge_private (hP : T.IsAcceptance P) {α : ℝ}
    (hgap : T.LojasiewiczData P α) {ψ : H} (hψ : ‖ψ‖ = 1) :
    16 * (T.accProbA P ψ - 3 / 2 * α) * (1 - T.accProbA P ψ) ≤ ‖T.gradAccA P ψ‖ ^ 2 := by
  rw [T.norm_gradAccA_sq hP hψ]
  have hq := hgap ψ hψ
  nlinarith

private abbrev FlowA (P : K →L[ℂ] K) (γ : ℝ → H) : Prop :=
  T.IsUnitFlowOn P γ (Ici 0)

variable {γ : ℝ → H}

/-- Along a local solution, acceptance has within-derivative equal to the squared
norm of its velocity, including at endpoints of the time interval. -/
theorem IsUnitFlowOn.hasDerivWithinAt_accProb {s : Set ℝ} (hγ : T.IsUnitFlowOn P γ s) (hP : T.IsAcceptance P)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivWithinAt (fun u => T.accProbA P (γ u)) (‖T.gradAccA P (γ t)‖ ^ 2) s t := by
  have h := (T.hasFDerivAt_accProbA hP (γ t)).comp_hasDerivWithinAt t (hγ.deriv t ht)
  convert h using 1
  · rfl
  · exact (TensorSquare.deriv_accProbA_gradAccA hP (hγ.sphere t ht)).symm

/-- `p` is nondecreasing along the flow. -/
private theorem flow_p_mono (hP : T.IsAcceptance P) (hγ : FlowA (T := T) P γ) :
    MonotoneOn (fun t => T.accProbA P (γ t)) (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · exact fun t ht => (hγ.hasDerivWithinAt_accProb hP ht).continuousWithinAt
  · intro t ht
    exact (hγ.hasDerivWithinAt_accProb hP (interior_subset ht)).mono interior_subset
  · intro t ht
    positivity

/-- `1 - p_t ≥ e^{-16 t} (1 - p_0)`: the flow never reaches `p = 1` in finite time
(uses `ṗ = 16(q - p²) ≤ 16(1 - p)` via `T.qProbA_le_accProbA` and `T.accProbA_le_one`). -/
private theorem flow_one_sub_p_ge (hP : T.IsAcceptance P) (hγ : FlowA (T := T) P γ)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    Real.exp (-(16 * t)) * (1 - T.accProbA P (γ 0)) ≤ 1 - T.accProbA P (γ t) := by
  let f := fun s => (1 - T.accProbA P (γ s)) * Real.exp (16 * s)
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivWithinAt f
        ((-‖T.gradAccA P (γ s)‖ ^ 2) * Real.exp (16 * s) +
          (1 - T.accProbA P (γ s)) * (Real.exp (16 * s) * 16)) (Ici 0) s := by
    apply ((hγ.hasDerivWithinAt_accProb hP hs).const_sub 1).mul
    simpa using (((hasDerivAt_id s).const_mul 16).exp.hasDerivWithinAt (s := Ici 0))
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun s hs => (hd s hs).continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).mono interior_subset
    · intro s hs
      have hu := hγ.sphere s (interior_subset hs)
      have hq := T.qProbA_le_accProbA hP hu
      have hp := T.accProbA_le_one hP hu
      have hn := T.norm_gradAccA_sq hP hu
      have hb : ‖T.gradAccA P (γ s)‖ ^ 2 ≤ 16 * (1 - T.accProbA P (γ s)) := by
        nlinarith [sq_nonneg (1 - T.accProbA P (γ s))]
      have he := mul_nonneg (Real.exp_pos (16 * s)).le (sub_nonneg.mpr hb)
      nlinarith
  have h := hm (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) ht ht
  have he : Real.exp (-(16 * t)) * Real.exp (16 * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(16 * t))).le
  dsimp [f] at hh
  simp only [mul_zero, Real.exp_zero, mul_one] at hh
  have heq : Real.exp (-(16 * t)) * ((1 - T.accProbA P (γ t)) * Real.exp (16 * t)) =
      1 - T.accProbA P (γ t) := by
    calc
      _ = (Real.exp (-(16 * t)) * Real.exp (16 * t)) * (1 - T.accProbA P (γ t)) := by ring
      _ = _ := by rw [he, one_mul]
  rwa [heq] at hh

/-- Under the spectral gap hypothesis, if `p_0 > 3α/2` then `p_t → 1` along the flow.
(If not, `p_t ≤ 1 - η` for some `η > 0` and all `t`, whence
`ṗ ≥ 16(p_0 - 3α/2)η > 0` uniformly, contradicting `p ≤ 1`.) -/
private theorem flow_p_tendsto_one (hP : T.IsAcceptance P) {α : ℝ}
    (hgap : T.LojasiewiczData P α) (hγ : FlowA (T := T) P γ)
    (h0 : 3 / 2 * α < T.accProbA P (γ 0)) :
    Filter.Tendsto (fun n : ℕ => T.accProbA P (γ n)) Filter.atTop (nhds 1) := by
  let p : ℕ → ℝ := fun n => T.accProbA P (γ n)
  have hm := flow_p_mono hP hγ
  have hmn : Monotone p := by
    intro m n hmn
    exact hm (by simp) (by simp) (by exact_mod_cast hmn)
  have hb : BddAbove (range p) := ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact T.accProbA_le_one hP (hγ.sphere n (by simp))⟩
  let L := ⨆ n, p n
  have hL : L ≤ 1 := ciSup_le fun n => T.accProbA_le_one hP (hγ.sphere n (by simp))
  have hpL (t : ℝ) (ht : 0 ≤ t) : T.accProbA P (γ t) ≤ L := by
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact (hm ht (by simp) hn).trans (le_ciSup hb n)
  have he : L = 1 := by
    by_contra hne
    have hlt : L < 1 := lt_of_le_of_ne hL hne
    let β := 16 * (T.accProbA P (γ 0) - 3 / 2 * α) * (1 - L)
    have hβ : 0 < β := by dsimp [β]; positivity
    have hd (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
        HasDerivWithinAt (fun t => T.accProbA P (γ t) - β * t)
          (‖T.gradAccA P (γ t)‖ ^ 2 - β) (Ici 0) t := by
      apply (hγ.hasDerivWithinAt_accProb hP ht).sub
      simpa using ((hasDerivAt_id t).const_mul β).hasDerivWithinAt (s := Ici 0)
    have hg : MonotoneOn (fun t => T.accProbA P (γ t) - β * t) (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      · exact fun t ht => (hd t ht).continuousWithinAt
      · exact fun t ht => (hd t (interior_subset ht)).mono interior_subset
      · intro t ht
        have ht' : 0 ≤ t := interior_subset ht
        have hlo := hm (by simp) ht' ht'
        have hup := hpL t ht'
        have hgap' := norm_gradAccA_sq_ge_private hP hgap (hγ.sphere t ht')
        have hm' := mul_le_mul (show T.accProbA P (γ 0) - 3 / 2 * α ≤
            T.accProbA P (γ t) - 3 / 2 * α by linarith)
          (show 1 - L ≤ 1 - T.accProbA P (γ t) by linarith)
          (by linarith : 0 ≤ 1 - L) (by linarith : 0 ≤ T.accProbA P (γ t) - 3 / 2 * α)
        dsimp [β]
        nlinarith
    let t := (2 - T.accProbA P (γ 0)) / β
    have ht : 0 ≤ t := div_nonneg (by
      linarith [T.accProbA_le_one hP (hγ.sphere 0 (by simp))]) hβ.le
    have hg' := hg (by simp) ht ht
    have hu := T.accProbA_le_one hP (hγ.sphere t ht)
    have he' : β * t = 2 - T.accProbA P (γ 0) := by
      dsimp [t]; field_simp
    simp only [mul_zero, sub_zero] at hg'
    linarith
  simpa [p, L, he] using tendsto_atTop_ciSup hmn hb

private theorem flow_chord_bound (hP : T.IsAcceptance P) {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : T.LojasiewiczData P α) (hγ : FlowA (T := T) P γ)
    (h0 : 3 / 2 * α < T.accProbA P (γ 0)) (h1 : T.accProbA P (γ 0) < 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖γ t - γ s‖ ≤
      Vpot (3 / 2 * α) (T.accProbA P (γ s)) - Vpot (3 / 2 * α) (T.accProbA P (γ t)) := by
  have _ := hα0
  let c := 3 / 2 * α
  have hc : c < 1 := h0.trans h1
  have hm := flow_p_mono hP hγ
  have hp (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) : T.accProbA P (γ r) ∈ Ioo c 1 := by
    constructor
    · exact h0.trans_le (hm (by simp) hr hr)
    · have h := flow_one_sub_p_ge hP hγ hr
      have he := mul_pos (Real.exp_pos (-(16 * r))) (sub_pos.mpr h1)
      linarith
  have hv (v : H) : AntitoneOn
      (fun r => (⟪v, γ r⟫_ℂ).re + ‖v‖ * Vpot c (T.accProbA P (γ r))) (Ici 0) := by
    let d := fun r => (⟪v, T.gradAccA P (γ r)⟫_ℂ).re + ‖v‖ *
      (-(1 / (4 * Real.sqrt ((T.accProbA P (γ r) - c) * (1 - T.accProbA P (γ r)))))) *
        ‖T.gradAccA P (γ r)‖ ^ 2
    have hd (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :
        HasDerivWithinAt (fun r => (⟪v, γ r⟫_ℂ).re + ‖v‖ * Vpot c (T.accProbA P (γ r)))
          (d r) (Ici 0) r := by
      have hi := (hasDerivWithinAt_const r (Ici 0) v).inner ℂ (hγ.deriv r hr)
      have hi' := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt r hi
      have hv' := (hasDerivAt_Vpot hc (hp r hr)).comp_hasDerivWithinAt r
        (hγ.hasDerivWithinAt_accProb hP hr)
      convert hi'.add (hv'.const_mul ‖v‖) using 1
      · rfl
      · simp [d, inner_zero_left, mul_assoc]
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun r hr => (hd r hr).continuousWithinAt
    · exact fun r hr => (hd r (interior_subset hr)).mono interior_subset
    · intro r hr
      have hr' := interior_subset hr
      have hpr := hp r hr'
      let A := Real.sqrt ((T.accProbA P (γ r) - c) * (1 - T.accProbA P (γ r)))
      have hA : 0 < A := Real.sqrt_pos.mpr
        (mul_pos (sub_pos.mpr hpr.1) (sub_pos.mpr hpr.2))
      have hAsq : A ^ 2 = (T.accProbA P (γ r) - c) * (1 - T.accProbA P (γ r)) :=
        Real.sq_sqrt (mul_pos (sub_pos.mpr hpr.1) (sub_pos.mpr hpr.2)).le
      have hg := norm_gradAccA_sq_ge_private hP hgap (hγ.sphere r hr')
      change 16 * (T.accProbA P (γ r) - c) * (1 - T.accProbA P (γ r)) ≤ _ at hg
      have hng := norm_nonneg (T.gradAccA P (γ r))
      have hb : 4 * A ≤ ‖T.gradAccA P (γ r)‖ := by nlinarith
      have hmul : ‖T.gradAccA P (γ r)‖ * (4 * A) ≤ ‖T.gradAccA P (γ r)‖ ^ 2 := by
        nlinarith [mul_nonneg hng (sub_nonneg.mpr hb)]
      have hdiv : ‖T.gradAccA P (γ r)‖ ≤ ‖T.gradAccA P (γ r)‖ ^ 2 / (4 * A) :=
        (le_div_iff₀ (by positivity)).mpr hmul
      have hi := re_inner_le_norm (𝕜 := ℂ) v (T.gradAccA P (γ r))
      change (⟪v, T.gradAccA P (γ r)⟫_ℂ).re ≤ ‖v‖ * ‖T.gradAccA P (γ r)‖ at hi
      have hmul' := mul_le_mul_of_nonneg_left hdiv (norm_nonneg v)
      dsimp [d]
      change (⟪v, T.gradAccA P (γ r)⟫_ℂ).re + ‖v‖ * (-(1 / (4 * A))) *
        ‖T.gradAccA P (γ r)‖ ^ 2 ≤ 0
      have heq : ‖v‖ * (-(1 / (4 * A))) * ‖T.gradAccA P (γ r)‖ ^ 2 =
          -(‖v‖ * (‖T.gradAccA P (γ r)‖ ^ 2 / (4 * A))) := by ring
      rw [heq]
      linarith
  have hh := hv (γ t - γ s) hs (le_trans hs hst) hst
  have hi : (⟪γ t - γ s, γ t⟫_ℂ).re - (⟪γ t - γ s, γ s⟫_ℂ).re =
      ‖γ t - γ s‖ ^ 2 := by
    rw [← Complex.sub_re, ← inner_sub_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hn := norm_nonneg (γ t - γ s)
  by_cases hz : ‖γ t - γ s‖ = 0
  · rw [hz]
    have hpst := hm hs (le_trans hs hst) hst
    unfold Vpot
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.arcsin_le_arcsin
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · have hn' : 0 < ‖γ t - γ s‖ := lt_of_le_of_ne hn (Ne.symm hz)
    have hineq : ‖γ t - γ s‖ ^ 2 ≤ ‖γ t - γ s‖ *
        (Vpot c (T.accProbA P (γ s)) - Vpot c (T.accProbA P (γ t))) := by linarith
    nlinarith

/-! ### F. Convergence to a limit in `G` -/

/-- The flow converges (along `ℕ`) to a unit vector `φ` with `p(φ) = 1` and
`‖γ 0 - φ‖ ≤ V(p_0)`. -/
private theorem flow_limit (hP : T.IsAcceptance P) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 2 / 3) (hgap : T.LojasiewiczData P α) (hγ : FlowA (T := T) P γ)
    (h0 : 3 / 2 * α < T.accProbA P (γ 0)) (h1 : T.accProbA P (γ 0) < 1) :
    ∃ φ : H, Filter.Tendsto (fun n : ℕ => γ n) Filter.atTop (nhds φ) ∧
      ‖φ‖ = 1 ∧ T.accProbA P φ = 1 ∧
      ‖γ 0 - φ‖ ≤ Vpot (3 / 2 * α) (T.accProbA P (γ 0)) := by
  have hc : 3 / 2 * α < 1 := by linarith only [hα]
  have hp := flow_p_tendsto_one hP hgap hγ h0
  have hv := Vpot_tendsto_zero hc hp
  have hch (m n : ℕ) (hmn : m ≤ n) :
      dist (γ m) (γ n) ≤ Vpot (3 / 2 * α) (T.accProbA P (γ m)) := by
    have hh := flow_chord_bound hP hα0 hgap hγ h0 h1
      (s := (m : ℝ)) (t := (n : ℝ)) (by positivity) (by exact_mod_cast hmn)
    have hn := Vpot_nonneg (c := 3 / 2 * α)
      (T.accProbA_le_one hP (hγ.sphere n (by simp)))
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  have hca : CauchySeq (fun n : ℕ => γ n) :=
    cauchySeq_of_le_tendsto_0' _ hch hv
  obtain ⟨φ, hφ⟩ := cauchySeq_tendsto_of_complete hca
  refine ⟨φ, hφ, ?_, ?_, ?_⟩
  · have hn := hφ.norm
    have he : (fun n : ℕ => ‖γ (n : ℝ)‖) = fun _ => (1 : ℝ) := by
      funext n; exact hγ.sphere n (by simp)
    rw [he] at hn
    exact tendsto_nhds_unique hn tendsto_const_nhds
  · have ha := (smooth_acc_private T (P := P)).continuous.continuousAt.tendsto.comp hφ
    exact tendsto_nhds_unique ha hp
  · have hh : Filter.Tendsto (fun n : ℕ => ‖γ 0 - γ (n : ℝ)‖) Filter.atTop
        (nhds ‖γ 0 - φ‖) := (tendsto_const_nhds.sub hφ).norm
    apply le_of_tendsto hh
    exact Filter.Eventually.of_forall fun n => by
      have h := hch 0 n (Nat.zero_le n)
      simpa [dist_eq_norm] using h

variable (T)

/-- **Theorem 3.4, angular conclusion from the moment inequality.** For a unit input with
acceptance greater than 3α/2, the gradient flow supplies a unit state accepted with certainty
whose projective angle with the input is at most the manuscript's half-arcsine potential. -/
theorem angular_witness_abstract (hP : T.IsAcceptance P) (hPnorm : ‖P‖ ≤ 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hdata : T.LojasiewiczData P α)
    {ψ : H} (hψ : ‖ψ‖ = 1) (hhigh : 3 / 2 * α < T.accProbA P ψ) :
    ∃ φ : H, ‖φ‖ = 1 ∧ T.accProbA P φ = 1 ∧
      Real.arccos ‖⟪ψ, φ⟫_ℂ‖ ≤ Vpot (3 / 2 * α) (T.accProbA P ψ) := by
  rcases eq_or_lt_of_le (T.accProbA_le_one hP hψ) with hperfect | hlt
  · refine ⟨ψ, hψ, hperfect, ?_⟩
    simp [inner_self_eq_norm_sq_to_K, hψ, hperfect]
  · obtain ⟨γ, hstart, hsphere, hderiv⟩ := T.exists_global_flowA hP hPnorm hψ
    have hγ : FlowA (T := T) P γ := ⟨hsphere, hderiv⟩
    have h0 : 3 / 2 * α < T.accProbA P (γ 0) := hstart.symm ▸ hhigh
    have h1 : T.accProbA P (γ 0) < 1 := hstart.symm ▸ hlt
    obtain ⟨φ, hlim, hφ, hpφ, _⟩ := flow_limit hP hα0 hα hdata hγ h0 h1
    refine ⟨φ, hφ, hpφ, ?_⟩
    let v (t : ℝ) := Vpot (3 / 2 * α) (T.accProbA P (γ t))
    have angle (n : ℕ) : Real.arccos ‖⟪γ 0, γ n⟫_ℂ‖ ≤ v 0 := by
      have hI : Icc (0 : ℝ) (n : ℝ) ⊆ Ici 0 := fun _ ht => ht.1
      have hpiece (s) (hs : s ∈ Icc (0 : ℝ) (n : ℝ)) (t)
          (_ : t ∈ Icc (0 : ℝ) (n : ℝ)) (hst : s ≤ t) : ‖γ s - γ t‖ ≤ v s - v t := by
        rw [norm_sub_rev]
        exact flow_chord_bound hP hα0 hdata hγ h0 h1 hs.1 hst
      have hangle := projective_angle_le_of_chord_bound (γ := γ) (v := v)
        (Nat.cast_nonneg n)
        (fun t ht => ((hderiv t (hI ht)).continuousWithinAt).mono hI)
        (fun t ht => hsphere t (hI ht)) hpiece
      exact hangle.trans (sub_le_self _ (Vpot_nonneg (T.accProbA_le_one hP (hsphere n (by simp)))))
    have hangle_lim : Filter.Tendsto (fun n : ℕ => Real.arccos ‖⟪γ 0, γ n⟫_ℂ‖)
        Filter.atTop (nhds (Real.arccos ‖⟪γ 0, φ⟫_ℂ‖)) :=
      (Real.continuous_arccos.tendsto _).comp (tendsto_const_nhds.inner hlim).norm
    simpa [v, hstart] using le_of_tendsto hangle_lim (Filter.Eventually.of_forall angle)

/-- **Theorem 3.4, linear consequence from moment data**: if `0 ≤ α < 2/3`,
acceptance at least `1 − ε` with `C_α ε < 1` gives squared overlap at least
`1 − C_α ε` with the certainty state supplied by the angular estimate. -/
theorem robust_testing_abstract (hP : T.IsAcceptance P) (hPnorm : ‖P‖ ≤ 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hdata : T.LojasiewiczData P α)
    {ψ : H} (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : Cgap α * ε < 1)
    (hp : 1 - ε ≤ T.accProbA P ψ) :
    ∃ φ : H, ‖φ‖ = 1 ∧ T.accProbA P φ = 1 ∧
      1 - Cgap α * ε ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  apply linear_witness_of_small_error hψ hα (T.accProbA_le_one hP hψ) hε0 hε hp
  exact T.angular_witness_abstract hP hPnorm hα0 hα hdata hψ

end TensorSquare

end

end GaussianTesting
