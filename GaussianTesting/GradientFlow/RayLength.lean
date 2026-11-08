module

public import GaussianTesting.GradientFlow.RayPathLength
public import GaussianTesting.GradientFlow.RayAcceptanceLimit

@[expose] public section

/-! # The path-length estimate in Theorem 3.4

The spectral gradient bound controls the length of a projective trajectory
by the decrease of the manuscript's half-arcsine potential. Differentiating
this antiderivative along acceptance evaluates the change of variables in
the manuscript's path-length integral.
-/

namespace GaussianTesting

open Set Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- The path-length integral in Theorem 3.4 is at most the decrease of its
half-arcsine potential between the two acceptance probabilities. -/
theorem ray_integral_speed_le_potential_sub (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ r in s..t, Real.sqrt ((hilbertTensorSquare H).rayGradientNormSq P (ρ r))) ≤
      Vpot (3 / 2 * α) ((hilbertTensorSquare H).rayAcceptance P (ρ s)) -
        Vpot (3 / 2 * α) ((hilbertTensorSquare H).rayAcceptance P (ρ t)) := by
  let p : ℝ → ℝ := fun r => (hilbertTensorSquare H).rayAcceptance P (ρ r)
  let g : ℝ → ℝ := fun r => (hilbertTensorSquare H).rayGradientNormSq P (ρ r)
  let c := 3 / 2 * α
  let A : ℝ → ℝ := fun r => Real.sqrt ((p r - c) * (1 - p r))
  have hc : c < 1 := hhigh.trans hlow
  have hI : Icc s t ⊆ Ici 0 := fun _ hr => hs.trans hr.1
  have hp (r : ℝ) (hr : r ∈ Icc s t) : p r ∈ Ioo c 1 := by
    refine ⟨hhigh.trans_le (hρ.rayAcceptance_mono hP (mem_Ici.mpr (le_refl (0 : ℝ)))
      (hI hr) (hI hr)), hρ.rayAcceptance_lt_one hP hlow (hI hr)⟩
  have hA (r : ℝ) (hr : r ∈ Icc s t) : 0 < A r :=
    Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr (hp r hr).1) (sub_pos.mpr (hp r hr).2))
  have hpcont : ContinuousOn p (Icc s t) :=
    fun r hr => ((hρ.hasDerivWithinAt_rayAcceptance hP (hI hr)).mono hI).continuousWithinAt
  have hgcont : ContinuousOn g (Icc s t) :=
    ((hilbertTensorSquare H).continuous_rayGradientNormSq P).comp_continuousOn
      (hρ.continuous.mono hI)
  have hAcont : ContinuousOn A (Icc s t) :=
    ((hpcont.sub continuousOn_const).mul (continuousOn_const.sub hpcont)).sqrt
  have hquot : ContinuousOn (fun r => g r / (4 * A r)) (Icc s t) :=
    hgcont.div (continuousOn_const.mul hAcont) (fun r hr => mul_ne_zero (by norm_num) (hA r hr).ne')
  have hd (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivWithinAt (fun r => -Vpot c (p r)) (g r / (4 * A r)) (Icc s t) r := by
    have h := ((hasDerivAt_Vpot hc (hp r hr)).comp_hasDerivWithinAt r
      ((hρ.hasDerivWithinAt_rayAcceptance hP (hI hr)).mono hI)).neg
    apply h.congr_deriv
    dsimp [A, g, p]
    ring
  have hint : (∫ r in s..t, g r / (4 * A r)) = Vpot c (p s) - Vpot c (p t) := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
      (fun r hr => (hd r hr).continuousWithinAt)
      (fun r hr => (hd r (mem_Icc_of_Ioo hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2))
      (hquot.intervalIntegrable_of_Icc hst)
    linarith
  change (∫ r in s..t, Real.sqrt (g r)) ≤ Vpot c (p s) - Vpot c (p t)
  rw [← hint]
  apply intervalIntegral.integral_mono_on hst
    (hgcont.sqrt.intervalIntegrable_of_Icc hst) (hquot.intervalIntegrable_of_Icc hst)
  intro r hr
  have hg0 : 0 ≤ g r := sq_nonneg _
  have hgsq : Real.sqrt (g r) ^ 2 = g r := Real.sq_sqrt hg0
  have hAsq : A r ^ 2 = (p r - c) * (1 - p r) :=
    Real.sq_sqrt (mul_pos (sub_pos.mpr (hp r hr).1) (sub_pos.mpr (hp r hr).2)).le
  have hbound := (ray_flow_derivative_bounds hP hα hspec hρ (hI hr)).2.2.1
  change 16 * (p r - c) * (1 - p r) ≤ g r at hbound
  have hroot : 4 * A r ≤ Real.sqrt (g r) := by
    nlinarith [Real.sqrt_nonneg (g r), (hA r hr).le]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (hA r hr))).mpr
  nlinarith [mul_nonneg (Real.sqrt_nonneg (g r)) (sub_nonneg.mpr hroot)]

/-- The manuscript's Fubini–Study distance estimate on every ordered
subinterval of the projective gradient trajectory. -/
theorem ray_dist_le_potential_sub (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    dist (ρ s) (ρ t) ≤ Vpot (3 / 2 * α) ((hilbertTensorSquare H).rayAcceptance P (ρ s)) -
      Vpot (3 / 2 * α) ((hilbertTensorSquare H).rayAcceptance P (ρ t)) :=
  (hρ.dist_le_integral_speed hP hst (fun _ hr => hs.trans hr.1)).trans
    (ray_integral_speed_le_potential_sub hP hα hspec hρ hhigh hlow hs hst)

end GaussianTesting
