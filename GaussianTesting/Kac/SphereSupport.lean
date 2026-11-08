module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereKacTransition

@[expose] public section

/-!
# Full support of normalized sphere measure

Every nonempty open subset of the sphere has positive normalized surface
measure. Consequently a nonzero continuous sphere function defines a nonzero
L² vector, as needed for the sharpness witness in Theorem 4.1.
-/

namespace GaussianTesting.SO3

open MeasureTheory

noncomputable section

instance sphereSurfaceMeasure_isOpenPosMeasure :
    sphereSurfaceMeasure.IsOpenPosMeasure := by
  unfold sphereSurfaceMeasure
  infer_instance

instance sphereMeasure_isOpenPosMeasure : sphereMeasure.IsOpenPosMeasure := by
  unfold sphereMeasure
  exact Measure.isOpenPosMeasure_smul sphereSurfaceMeasure
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

/-- Continuous sphere functions remain distinct in the normalized L² space. -/
theorem sphereContinuousToLp_injective : Function.Injective sphereContinuousToLp :=
  ContinuousMap.toLp_injective sphereMeasure

/-- A continuous function nonzero at one point is a nonzero L² vector. -/
theorem sphereContinuousToLp_ne_zero_of_apply_ne_zero
    (f : C(Sphere, ℂ)) (x : Sphere) (hx : f x ≠ 0) :
    sphereContinuousToLp f ≠ 0 := by
  intro hf
  have he : f = 0 := sphereContinuousToLp_injective (hf.trans (map_zero _).symm)
  exact hx (congrArg (fun h : C(Sphere, ℂ) => h x) he)

end
end GaussianTesting.SO3
