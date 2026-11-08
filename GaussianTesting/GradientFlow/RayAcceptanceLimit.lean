module

public import GaussianTesting.GradientFlow.RayNonattainment
public import GaussianTesting.GradientFlow.RayConvergence

@[expose] public section

/-! # Strict increase of acceptance to certainty

The paragraph after Eq. (3.7), in the proof of Theorem 3.4. For any
projective trajectory starting with 3α/2 < p₀ < 1, the exponential lower
bound on rejection keeps acceptance below one. Equation (3.7) then gives
a positive derivative, and bounded monotonicity forces the limit to be one.
-/

namespace GaussianTesting

open Set Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- Above the spectral threshold and below certainty, acceptance strictly
increases on the whole forward half-line, including comparisons with time zero. -/
theorem rayAcceptance_strictMonoOn (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1) :
    StrictMonoOn (fun t => (hilbertTensorSquare H).rayAcceptance P (ρ t)) (Ici 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
  · exact fun t ht => (hρ.hasDerivWithinAt_rayAcceptance hP ht).continuousWithinAt
  · exact fun t ht => (hρ.hasDerivWithinAt_rayAcceptance hP (interior_subset ht)).mono interior_subset
  · intro t ht
    have ht0 : 0 ≤ t := interior_subset ht
    obtain ⟨_, _, hbound, hinit⟩ := ray_flow_derivative_bounds hP hα hspec hρ ht0
    have hp := hρ.rayAcceptance_lt_one hP hlow ht0
    exact lt_of_lt_of_le
      (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hhigh)) (sub_pos.mpr hp))
      (hinit.trans hbound)

/-- The claim immediately after Eq. (3.7) in Theorem 3.4. For every forward
projective trajectory with 3α/2 < p₀ < 1, acceptance is strictly increasing,
remains below one at every finite time, and tends to one in continuous time. -/
theorem ray_acceptance_strictly_increases_to_one (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1) :
    let p := fun t => (hilbertTensorSquare H).rayAcceptance P (ρ t)
    (∀ t ≥ 0, p t < 1) ∧ StrictMonoOn p (Ici 0) ∧ Tendsto p atTop (𝓝 1) :=
  ⟨fun _ ht => hρ.rayAcceptance_lt_one hP hlow ht,
    rayAcceptance_strictMonoOn hP hα hspec hρ hhigh hlow,
    rayAcceptance_tendsto_one hP hα hspec hρ hhigh⟩

end GaussianTesting
