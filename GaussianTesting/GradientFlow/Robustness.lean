module

/-
Finite-dimensional linear-fidelity consequence of Theorem 3.4
(`thm:bound-fidelity-gradient-flow`) in `material/manuscript.tex`.
The acceptance error `ε` below is the parameter `τ` in the manuscript.

The gradient flow supplies a state accepted with certainty whose angle with the
input is bounded by the half-arcsine potential. The half-angle formula for cosine
gives the squared-overlap lower bound for that same state. The robustness
constant and this trigonometric implication are used by the manuscript's
completed projective-flow proof in `HilbertSpectralGap.lean`. The finite
small-error theorem below is an earlier coordinate interface.
-/
public import GaussianTesting.GradientFlow.Flow

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace
open Finset

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The robustness constant `C_α = 1/(1 - 3α/2)` of Theorem 3.4. -/
def Cgap (α : ℝ) : ℝ := (1 - 3 / 2 * α)⁻¹

@[simp] lemma Cgap_seventwelfths : Cgap (7 / 12) = 8 := by norm_num [Cgap]

/-- The half-angle implication in the proof of Theorem 3.4. For
`x = Cgap α * (1 - p)` in `[0, 1]`, the angular estimate gives
`r² ≥ cos²(arcsin(√x)/2) = (1 + √(1-x))/2 ≥ 1-x`. -/
theorem linear_bound_of_Vpot_angle {α p r : ℝ} (hα : α < 2 / 3)
    (hhigh : 3 / 2 * α < p) (hp : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hangle : Real.arccos r ≤ Vpot (3 / 2 * α) p) :
    1 - Cgap α * (1 - p) ≤ r ^ 2 := by
  have hden : 0 < 1 - 3 / 2 * α := by linarith
  let x := (1 - p) / (1 - 3 / 2 * α)
  have hx : Cgap α * (1 - p) = x := by simp only [x, Cgap, div_eq_mul_inv, mul_comm]
  have hx0 : 0 ≤ x := div_nonneg (sub_nonneg.mpr hp) hden.le
  have hx1 : x ≤ 1 := (div_le_one hden).mpr (by linarith)
  let θ := Vpot (3 / 2 * α) p
  have hθ0 : 0 ≤ θ := Vpot_nonneg hp
  have hθπ : θ ≤ Real.pi / 4 := Vpot_le_pi_div_four _ _
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg r)
    (by linarith [Real.pi_pos] : θ ≤ Real.pi) hangle
  rw [Real.cos_arccos (by linarith) hr1] at hcos
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hhalf := Real.cos_two_mul θ
  have htwice : 2 * θ = Real.arcsin (Real.sqrt x) := by dsimp [θ, Vpot, x]; ring
  rw [htwice, Real.cos_arcsin, Real.sq_sqrt hx0] at hhalf
  have hsqrt : Real.sqrt (1 - x) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  rw [hx]
  apply le_trans _ ((sq_le_sq₀ hcos0 hr).mpr hcos)
  nlinarith [Real.sq_sqrt (sub_nonneg.mpr hx1),
    mul_nonneg (Real.sqrt_nonneg (1 - x)) (sub_nonneg.mpr hsqrt)]

/-- Convert a high-acceptance angular witness to the small-error linear witness,
using the actual deficit `1 - p ψ` before passing to its upper bound `ε`. -/
theorem linear_witness_of_small_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {p : E → ℝ} {ψ : E} (hψ : ‖ψ‖ = 1)
    {α ε : ℝ} (hα : α < 2 / 3) (hp1 : p ψ ≤ 1)
    (hε0 : 0 ≤ ε) (hε : Cgap α * ε < 1) (hp : 1 - ε ≤ p ψ)
    (hw : 3 / 2 * α < p ψ → ∃ φ : E, ‖φ‖ = 1 ∧ p φ = 1 ∧
      Real.arccos ‖inner ℂ ψ φ‖ ≤ Vpot (3 / 2 * α) (p ψ)) :
    ∃ φ : E, ‖φ‖ = 1 ∧ p φ = 1 ∧ 1 - Cgap α * ε ≤ ‖inner ℂ ψ φ‖ ^ 2 := by
  have hden : 0 < 1 - 3 / 2 * α := by linarith
  have hC : 0 ≤ Cgap α := (inv_pos.mpr hden).le
  have hε' : ε / (1 - 3 / 2 * α) < 1 := by
    simpa only [Cgap, div_eq_mul_inv, mul_comm] using hε
  have hhigh : 3 / 2 * α < p ψ := by linarith [(div_lt_one hden).mp hε']
  obtain ⟨φ, hφ, hpφ, hang⟩ := hw hhigh
  refine ⟨φ, hφ, hpφ, ?_⟩
  have hr1 : ‖inner ℂ ψ φ‖ ≤ 1 := by
    simpa [hψ, hφ] using norm_inner_le_norm (𝕜 := ℂ) ψ φ
  have hdef : 1 - p ψ ≤ ε := by linarith
  have hle : Cgap α * (1 - p ψ) ≤ Cgap α * ε := by
    simpa only [mul_comm (Cgap α)] using mul_le_mul hdef (le_refl (Cgap α)) hC hε0
  exact (sub_le_sub_left hle 1).trans
    (linear_bound_of_Vpot_angle hα hhigh hp1 (norm_nonneg _) hr1 hang)

/-- **Theorem 3.4, finite-dimensional linear consequence** (thm:bound-fidelity-gradient-flow).
Note `G = {φ : ‖φ‖ = 1, p(φ) = 1}` appears through the existential conclusion. -/
theorem robust_testing_of_gap {P : H2 ι →ₗ[ℂ] H2 ι} (hP : IsAcceptanceProjection P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hgap : SpectralGapHyp P α)
    {ψ : H ι} (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : Cgap α * ε < 1)
    (hp : 1 - ε ≤ accProb P ψ) :
    ∃ φ : H ι, ‖φ‖ = 1 ∧ accProb P φ = 1 ∧ 1 - Cgap α * ε ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  apply linear_witness_of_small_error hψ hα (accProb_le_one hP hψ) hε0 hε hp
  exact angular_witness_of_gap hP hα0 hα hgap hψ

end

end GaussianTesting
