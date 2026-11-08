module

public import GaussianTesting.Fidelity
public import GaussianTesting.GradientFlow.Abstract

@[expose] public section

/-!
# Sharp angular and linear robustness

Theorem 3.4 uses one state accepted with certainty for both its angular estimate
and its linear estimate at every admissible error. Theorem 1.2 extracts the
linear bound for fidelity with the certainty set.
-/

namespace GaussianTesting

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The two conclusions of manuscript Theorem 3.4 for a single comparison state.
The angle bound is conditional on high acceptance, and the witness is chosen
before the error parameter in the linear bound. -/
def RobustnessBounds (p : E → ℝ) (α : ℝ) (ψ : E) : Prop :=
  ∃ φ ∈ certaintyStates p,
    Real.arccos (pureFidelity (certaintyStates p) ψ) ≤ Real.arccos ‖⟪ψ, φ⟫_ℂ‖ ∧
    (3 / 2 * α < p ψ →
      Real.arccos ‖⟪ψ, φ⟫_ℂ‖ ≤ Real.arcsin (Real.sqrt (Cgap α * (1 - p ψ))) / 2) ∧
    (∀ τ : ℝ, 0 ≤ τ → 1 - τ ≤ p ψ → 1 - Cgap α * τ ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2) ∧
    ‖⟪ψ, φ⟫_ℂ‖ ^ 2 ≤ pureFidelity (certaintyStates p) ψ ^ 2

/-- A certainty-state angular witness gives both conclusions of Theorem 3.4.
The cosine estimate gives the linear bound for the same witness at every
admissible error; below the threshold, the linear bound is nonpositive. -/
theorem bounds_of_angular_witness {p : E → ℝ} {α : ℝ} {ψ : E} (hψ : ‖ψ‖ = 1)
    (hα : α < 2 / 3) (hp : p ψ ≤ 1) (hne : (certaintyStates p).Nonempty)
    (hw : 3 / 2 * α < p ψ → ∃ φ ∈ certaintyStates p,
      Real.arccos ‖⟪ψ, φ⟫_ℂ‖ ≤ Vpot (3 / 2 * α) (p ψ)) : RobustnessBounds p α ψ := by
  have hden : 0 < 1 - 3 / 2 * α := by linarith
  have hC : 0 ≤ Cgap α := (inv_pos.mpr hden).le
  have hunit : ∀ φ ∈ certaintyStates p, ‖φ‖ = 1 := fun _ h => h.1
  have hchoose : ∃ φ ∈ certaintyStates p,
      (3 / 2 * α < p ψ → Real.arccos ‖⟪ψ, φ⟫_ℂ‖ ≤
        Real.arcsin (Real.sqrt (Cgap α * (1 - p ψ))) / 2) ∧
      1 - Cgap α * (1 - p ψ) ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
    by_cases hhigh : 3 / 2 * α < p ψ
    · obtain ⟨φ, hφ, hangle⟩ := hw hhigh
      have hang : Real.arccos ‖⟪ψ, φ⟫_ℂ‖ ≤ Real.arcsin (Real.sqrt (Cgap α * (1 - p ψ))) / 2 := by
        simpa only [Vpot, Cgap, div_eq_mul_inv (1 - p ψ), mul_comm (1 - p ψ)] using hangle
      have hr1 : ‖⟪ψ, φ⟫_ℂ‖ ≤ 1 := by
        simpa [hψ, hunit φ hφ] using norm_inner_le_norm (𝕜 := ℂ) ψ φ
      exact ⟨φ, hφ, fun _ => hang,
        linear_bound_of_Vpot_angle hα hhigh hp (norm_nonneg _) hr1 hangle⟩
    · obtain ⟨φ, hφ⟩ := hne
      refine ⟨φ, hφ, fun h => (hhigh h).elim, ?_⟩
      have hx : 1 ≤ Cgap α * (1 - p ψ) := by
        rw [Cgap, mul_comm, ← div_eq_mul_inv, one_le_div hden]
        linarith [le_of_not_gt hhigh]
      exact (sub_nonpos.mpr hx).trans (sq_nonneg _)
  obtain ⟨φ, hφ, hangle, hlin⟩ := hchoose
  refine ⟨φ, hφ, Real.arccos_le_arccos (overlap_le_pureFidelity hunit hφ), hangle, ?_,
    sq_overlap_le_pureFidelity_sq hunit hφ⟩
  intro τ _ hτ
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left (by linarith : 1 - p ψ ≤ τ) hC) 1).trans hlin

/-- Taking fidelity with the certainty set in Theorem 3.4 gives the conclusion
of informal Theorem 1.2. -/
theorem RobustnessBounds.linear_fidelity {p : E → ℝ} {α : ℝ} {ψ : E}
    (h : RobustnessBounds p α ψ) {τ : ℝ} (hτ : 0 ≤ τ) (hp : 1 - τ ≤ p ψ) :
    1 - Cgap α * τ ≤ pureFidelity (certaintyStates p) ψ ^ 2 := by
  obtain ⟨_, _, _, _, hlin, hfid⟩ := h
  exact (hlin τ hτ hp).trans hfid

/-- The angular estimate for the witness bounds the angle to the whole certainty set. -/
theorem RobustnessBounds.angular_fidelity {p : E → ℝ} {α : ℝ} {ψ : E}
    (h : RobustnessBounds p α ψ) (hp : 3 / 2 * α < p ψ) :
    Real.arccos (pureFidelity (certaintyStates p) ψ) ≤
      Real.arcsin (Real.sqrt (Cgap α * (1 - p ψ))) / 2 := by
  obtain ⟨_, _, hfid, hang, _, _⟩ := h
  exact hfid.trans (hang hp)

/-- Theorem 3.4, both bounds in the finite model under the polynomial gap hypothesis. -/
theorem robust_testing_of_gap_sharp {ι : Type*} [Fintype ι]
    {P : H2 ι →ₗ[ℂ] H2 ι} (hP : IsAcceptanceProjection P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hgap : SpectralGapHyp P α)
    (hne : (certaintyStates (accProb P)).Nonempty) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    RobustnessBounds (accProb P) α ψ := by
  apply bounds_of_angular_witness hψ hα (accProb_le_one hP hψ) hne
  intro hhigh
  obtain ⟨φ, hφ, hpφ, hang⟩ := angular_witness_of_gap hP hα0 hα hgap hψ hhigh
  exact ⟨φ, ⟨hφ, hpφ⟩, hang⟩

/-- Theorem 1.2, the linear fidelity consequence of Theorem 3.4 in the finite model. -/
theorem testing_fidelity_of_gap {ι : Type*} [Fintype ι]
    {P : H2 ι →ₗ[ℂ] H2 ι} (hP : IsAcceptanceProjection P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hgap : SpectralGapHyp P α)
    (hne : (certaintyStates (accProb P)).Nonempty) {ψ : H ι} (hψ : ‖ψ‖ = 1)
    {τ : ℝ} (hτ : 0 ≤ τ) (hp : 1 - τ ≤ accProb P ψ) :
    1 - Cgap α * τ ≤ pureFidelity (certaintyStates (accProb P)) ψ ^ 2 :=
  (robust_testing_of_gap_sharp hP hα0 hα hgap hne hψ).linear_fidelity hτ hp

namespace TensorSquare

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace E] [CompleteSpace K] (T : TensorSquare E K)

/-- Theorem 3.4 on a Hilbert tensor square supplied with the three-copy moment bound. -/
theorem robust_testing_abstract_sharp {P : K →L[ℂ] K} (hP : T.IsAcceptance P) (hPnorm : ‖P‖ ≤ 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hdata : T.LojasiewiczData P α)
    (hne : (certaintyStates (T.accProbA P)).Nonempty) {ψ : E} (hψ : ‖ψ‖ = 1) :
    RobustnessBounds (T.accProbA P) α ψ := by
  apply bounds_of_angular_witness hψ hα (T.accProbA_le_one hP hψ) hne
  intro hhigh
  obtain ⟨φ, hφ, hpφ, hang⟩ := T.angular_witness_abstract hP hPnorm hα0 hα hdata hψ hhigh
  exact ⟨φ, ⟨hφ, hpφ⟩, hang⟩

/-- Theorem 1.2 on the Hilbert tensor square, with the same moment input as Theorem 3.4. -/
theorem testing_fidelity_abstract {P : K →L[ℂ] K} (hP : T.IsAcceptance P) (hPnorm : ‖P‖ ≤ 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hdata : T.LojasiewiczData P α)
    (hne : (certaintyStates (T.accProbA P)).Nonempty) {ψ : E} (hψ : ‖ψ‖ = 1)
    {τ : ℝ} (hτ : 0 ≤ τ) (hp : 1 - τ ≤ T.accProbA P ψ) :
    1 - Cgap α * τ ≤ pureFidelity (certaintyStates (T.accProbA P)) ψ ^ 2 :=
  (T.robust_testing_abstract_sharp hP hPnorm hα0 hα hdata hne hψ).linear_fidelity hτ hp

end TensorSquare

end GaussianTesting
