module

public import GaussianTesting.GradientFlow.HilbertGradientBound
public import GaussianTesting.GradientFlow.RayEnergyIdentity

@[expose] public section

/-! # The differential inequality for ray acceptance

Equation (3.7) follows by evaluating Lemma 3.3 on the moving ray. The energy
identity makes acceptance nondecreasing, so its initial value also gives a
lower bound on its derivative.
-/

namespace GaussianTesting

open Set Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- The pointwise lower bound in Eq. (3.7). Under the spectral hypothesis for the
three-copy average, Lemma 3.3 bounds the squared gradient norm at every ray. -/
theorem rayGradientNormSq_ge_of_threeCopy_spectrum (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Set.Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    (q : Projectivization ℂ H) :
    16 * ((hilbertTensorSquare H).rayAcceptance P q - 3 / 2 * α) *
      (1 - (hilbertTensorSquare H).rayAcceptance P q) ≤
      (hilbertTensorSquare H).rayGradientNormSq P q :=
  norm_gradAcc_sq_ge_of_threeCopy_spectrum hP hα hspec (norm_rayUnitRep q)

/-- Eq. (3.7). The derivative of acceptance equals the squared Fubini–Study
speed and the squared gradient norm. Its spectral lower bound at time `t`
is at least the bound obtained by replacing the first factor by its value
at time zero. All derivatives and speed limits are relative to forward time. -/
theorem ray_flow_derivative_bounds (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    let p := fun r => (hilbertTensorSquare H).rayAcceptance P (ρ r)
    let g₂ := (hilbertTensorSquare H).rayGradientNormSq P (ρ t)
    HasDerivWithinAt p g₂ (Ici 0) t ∧
      Tendsto (fun r => dist (ρ r) (ρ t) / |r - t|) (𝓝[Ici 0 \ {t}] t) (𝓝 (Real.sqrt g₂)) ∧
      16 * (p t - 3 / 2 * α) * (1 - p t) ≤ g₂ ∧
      16 * (p 0 - 3 / 2 * α) * (1 - p t) ≤ 16 * (p t - 3 / 2 * α) * (1 - p t) := by
  refine ⟨hρ.hasDerivWithinAt_rayAcceptance hP ht, hρ.tendsto_dist_div_time hP ht,
    rayGradientNormSq_ge_of_threeCopy_spectrum hP hα hspec (ρ t), ?_⟩
  have hmono := hρ.rayAcceptance_mono hP (mem_Ici.mpr (le_refl (0 : ℝ))) ht ht
  have hp1 : (hilbertTensorSquare H).rayAcceptance P (ρ t) ≤ 1 :=
    (hilbertTensorSquare H).accProbA_le_one hP (norm_rayUnitRep _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hmono _) (by norm_num)) (sub_nonneg.mpr hp1)

end GaussianTesting
