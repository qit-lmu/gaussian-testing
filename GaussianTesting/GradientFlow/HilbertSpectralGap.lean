module

public import GaussianTesting.GradientFlow.HilbertGradientBound
public import GaussianTesting.GradientFlow.RayTrajectoryLimit
public import GaussianTesting.GradientFlow.ProjectiveGradientFlow
public import GaussianTesting.GradientFlow.SharpRobustness

@[expose] public section

/-!
# Theorem 3.4 from the projective gradient flow

The spectral bound controls the length of the projective gradient trajectory.
Its certainty limit gives the angular witness. The manuscript's cosine estimate
then gives the linear bound for the same witness at every admissible error.
-/

namespace GaussianTesting

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- The angular witness in Theorem 3.4 is a normalized representative of the
projective certainty limit, or the initial state itself when already certain. -/
theorem angular_witness_of_threeCopy_spectrum (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {ψ : H} (hψ : ‖ψ‖ = 1) (hhigh : 3 / 2 * α < (hilbertTensorSquare H).accProbA P ψ) :
    ∃ φ ∈ certaintyStates ((hilbertTensorSquare H).accProbA P),
      Real.arccos ‖⟪ψ, φ⟫_ℂ‖ ≤ Vpot (3 / 2 * α) ((hilbertTensorSquare H).accProbA P ψ) := by
  rcases eq_or_lt_of_le ((hilbertTensorSquare H).accProbA_le_one hP hψ) with hperfect | hlt
  · refine ⟨ψ, ⟨hψ, hperfect⟩, ?_⟩
    simp [inner_self_eq_norm_sq_to_K, hψ, hperfect]
  · have hnψ : ψ ≠ 0 := by intro h; simp [h] at hψ
    obtain ⟨ρ, hstart, hρ, _, _⟩ := projective_gradient_flow hP (Projectivization.mk ℂ ψ hnψ)
    have hp0 : (hilbertTensorSquare H).rayAcceptance P (ρ 0) =
        (hilbertTensorSquare H).accProbA P ψ := by
      rw [hstart, (hilbertTensorSquare H).rayAcceptance_mk P ψ hψ]
    obtain ⟨φ, hφ, _, hdist⟩ := ray_trajectory_tendsto_certaintyState hP
      ⟨hα0, by linarith only [hα]⟩ hspec hρ (by rwa [hp0]) (by rwa [hp0])
    refine ⟨φ, hφ, ?_⟩
    have hbound := hdist 0 le_rfl
    rw [hp0] at hbound
    simpa only [hstart, dist_ray_eq, rayDist_mk _ _ hψ hφ.1] using hbound

/-- Theorem 3.4, using the projective trajectory and its certainty limit.
Both estimates use the same certainty state, chosen before the error parameter. -/
theorem robustness_of_threeCopy_spectrum (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    (hne : (certaintyStates ((hilbertTensorSquare H).accProbA P)).Nonempty)
    {ψ : H} (hψ : ‖ψ‖ = 1) : RobustnessBounds ((hilbertTensorSquare H).accProbA P) α ψ := by
  apply bounds_of_angular_witness hψ hα ((hilbertTensorSquare H).accProbA_le_one hP hψ) hne
  exact angular_witness_of_threeCopy_spectrum hP hα0 hα hspec hψ

/-- The angular fidelity conclusion of Theorem 3.4. High acceptance itself
supplies a certainty state through the projective limit. -/
theorem angular_fidelity_of_threeCopy_spectrum (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {ψ : H} (hψ : ‖ψ‖ = 1) (hhigh : 3 / 2 * α < (hilbertTensorSquare H).accProbA P ψ) :
    Real.arccos (pureFidelity (certaintyStates ((hilbertTensorSquare H).accProbA P)) ψ) ≤
      Real.arcsin (Real.sqrt (Cgap α * (1 - (hilbertTensorSquare H).accProbA P ψ))) / 2 := by
  obtain ⟨φ, hφ, hang⟩ := angular_witness_of_threeCopy_spectrum hP hα0 hα hspec hψ hhigh
  have hfid := Real.arccos_le_arccos (overlap_le_pureFidelity (ψ := ψ) (fun _ h => h.1) hφ)
  exact hfid.trans (by
    simpa only [Vpot, Cgap, div_eq_mul_inv, mul_comm] using hang)

/-- Theorem 1.2, the linear fidelity conclusion of Theorem 3.4. -/
theorem testing_fidelity_of_threeCopy_spectrum (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    (hne : (certaintyStates ((hilbertTensorSquare H).accProbA P)).Nonempty)
    {ψ : H} (hψ : ‖ψ‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) (hp : 1 - τ ≤ (hilbertTensorSquare H).accProbA P ψ) :
    1 - Cgap α * τ ≤ pureFidelity (certaintyStates ((hilbertTensorSquare H).accProbA P)) ψ ^ 2 :=
  (robustness_of_threeCopy_spectrum hP hα0 hα hspec hne hψ).linear_fidelity hτ hp

end GaussianTesting
