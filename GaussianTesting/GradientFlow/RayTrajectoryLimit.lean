module

public import GaussianTesting.GradientFlow.RayLength
public import GaussianTesting.GradientFlow.RayCertaintyLimit
public import GaussianTesting.Fidelity

@[expose] public section

/-! # Convergence of the projective trajectory in Theorem 3.4

Above the spectral threshold and below certainty, the path-length estimate
bounds every tail by the half-arcsine potential. Acceptance tends to one,
so these tails shrink to zero. Completeness gives a limit ray, and continuity
of acceptance puts that ray in the certainty set.
-/

namespace GaussianTesting

open Set Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- The distance estimate used to prove the Cauchy property in Theorem 3.4. -/
theorem ray_dist_le_potential (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    dist (ρ s) (ρ t) ≤ Vpot (3 / 2 * α) ((hilbertTensorSquare H).rayAcceptance P (ρ s)) :=
  (ray_dist_le_potential_sub hP hα hspec hρ hhigh hlow hs hst).trans
    (sub_le_self _ (Vpot_nonneg ((hilbertTensorSquare H).accProbA_le_one hP (norm_rayUnitRep _))))

/-- Above threshold, a projective trajectory starting below certainty is
Cauchy as real time tends to infinity. -/
theorem ray_trajectory_cauchy (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1) :
    Cauchy (map ρ atTop) :=
  TensorSquare.cauchy_ray_of_dist_le_potential (hhigh.trans hlow)
    (rayAcceptance_tendsto_one hP hα hspec hρ hhigh)
    (fun _ _ hs hst => ray_dist_le_potential hP hα hspec hρ hhigh hlow hs hst)

/-- Theorem 3.4's projective flow converges to a certainty ray. Its distance
from every earlier point satisfies the manuscript's half-arcsine bound. -/
theorem ray_trajectory_tendsto_certainty (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1) :
    ∃ q : Projectivization ℂ H, Tendsto ρ atTop (𝓝 q) ∧
      (hilbertTensorSquare H).rayAcceptance P q = 1 ∧
      ∀ s ≥ 0, dist (ρ s) q ≤ Vpot (3 / 2 * α) ((hilbertTensorSquare H).rayAcceptance P (ρ s)) :=
  TensorSquare.exists_certainty_limit_of_dist_le_potential hP (hhigh.trans hlow)
    (rayAcceptance_tendsto_one hP hα hspec hρ hhigh)
    (fun _ _ hs hst => ray_dist_le_potential hP hα hspec hρ hhigh hlow hs hst)

/-- A normalized representative of the limiting ray belongs to the certainty
set used in the manuscript's fidelity definition. -/
theorem ray_trajectory_tendsto_certaintyState (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1) :
    ∃ (φ : H) (hφ : φ ∈ certaintyStates ((hilbertTensorSquare H).accProbA P)),
      let q := Projectivization.mk ℂ φ (by intro h; simpa [h] using hφ.1)
      Tendsto ρ atTop (𝓝 q) ∧
        ∀ s ≥ 0, dist (ρ s) q ≤ Vpot (3 / 2 * α) ((hilbertTensorSquare H).rayAcceptance P (ρ s)) := by
  obtain ⟨q, hq, hacc, hdist⟩ := ray_trajectory_tendsto_certainty hP hα hspec hρ hhigh hlow
  refine ⟨rayUnitRep q, ⟨norm_rayUnitRep q, hacc⟩, ?_⟩
  simpa only [mk_rayUnitRep] using And.intro hq hdist

end GaussianTesting
