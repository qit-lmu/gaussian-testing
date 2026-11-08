module

public import GaussianTesting.GradientFlow.RayEnergyIdentity

@[expose] public section

/-! # Path length of a projective gradient trajectory

The Fubini–Study distance between two trajectory points is at most the
integral of speed. A horizontal lift expresses speed as the norm of the
field of Eq. (3.4), and the partition argument for angles gives the bound.
-/

namespace GaussianTesting.TensorSquare

open Set Filter Topology

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K} {ρ : ℝ → Projectivization ℂ H}

/-- The phase-independent squared norm of the gradient is continuous on rays. -/
theorem continuous_rayGradientNormSq (T : TensorSquare H K) (P : K →L[ℂ] K) :
    Continuous (T.rayGradientNormSq P) := by
  apply isQuotientMap_rayMk.continuous_iff.mpr
  have hfun : T.rayGradientNormSq P ∘ (Projectivization.mk' ℂ) =
      (fun x : {x : H // x ≠ 0} => ‖T.gradAccA P (rayChartSection x)‖ ^ 2) := by
    funext x
    change T.rayGradientNormSq P (Projectivization.mk ℂ (x : H) x.property) = _
    rw [← mk_rayChartSection (x : H) x.property,
      T.rayGradientNormSq_mk P _ (norm_rayChartSection _ x.property)]
  rw [hfun]
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((T.contDiff_gradAccA P).continuous.continuousAt.comp
    ((contDiffAt_rayChartSection (x : H) x.property).continuousAt.comp
      continuous_subtype_val.continuousAt)).norm.pow 2

/-- The distance between any two points of a projective solution is at most
its integrated Fubini–Study speed, the first estimate in Theorem 3.4's path-length argument. -/
theorem IsProjectiveFlowOn.dist_le_integral_speed {s : Set ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ s) (hP : T.IsAcceptance P)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    dist (ρ a) (ρ b) ≤ ∫ t in a..b, Real.sqrt (T.rayGradientNormSq P (ρ t)) := by
  obtain ⟨γ, _, hγ, hrep⟩ := hρ.exists_unit_lift_Icc hP hab hI (rayUnitRep (ρ a))
    (norm_rayUnitRep _) (fun _ => (mk_rayUnitRep _).symm)
  have hne (t : ℝ) (ht : t ∈ Icc a b) : γ t ≠ 0 := fun h => by
    simpa [h] using hγ.sphere t ht
  have hint : (∫ t in a..b, Real.sqrt (T.rayGradientNormSq P (ρ t))) =
      ∫ t in a..b, ‖T.gradAccA P (γ t)‖ := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro t ht
    dsimp only
    rw [hrep t ht (hne t ht), T.rayGradientNormSq_mk P _ (hγ.sphere t ht),
      Real.sqrt_sq (norm_nonneg _)]
  rw [hint, dist_ray_eq, hrep a (left_mem_Icc.mpr hab) (hne a (left_mem_Icc.mpr hab)),
    hrep b (right_mem_Icc.mpr hab) (hne b (right_mem_Icc.mpr hab)),
    rayDist_mk _ _ (hγ.sphere a (left_mem_Icc.mpr hab)) (hγ.sphere b (right_mem_Icc.mpr hab))]
  exact hγ.angle_le_integral_speed hab Subset.rfl

end GaussianTesting.TensorSquare
