module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section

/-!
# The natural rotation action on the sphere's L² space

The spherical realization in Section 4 uses complex `L²(S²)` with normalized
surface measure. The natural unitary action is inverse pullback:
`(π(g)f)(x) = f(g⁻¹x)`. Preservation of the surface measure makes this action
unitary, and continuity of the rotations gives strong continuity on all of L².
This file supplies only the representation needed for the precise spherical
Kac spectral-gap calculation; it does not identify the Kac transition operator.
-/

namespace GaussianTesting.SO3

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Complex square-integrable functions on the unit two-sphere with normalized surface measure. -/
abbrev SphereSpace := Lp ℂ 2 sphereMeasure

private theorem sphere_pullback_mul (g h : Group) (f : SphereSpace) :
    Lp.compMeasurePreserving (sphereRotation g) (sphereRotation_measurePreserving g)
      (Lp.compMeasurePreserving (sphereRotation h) (sphereRotation_measurePreserving h) f) =
    Lp.compMeasurePreserving (sphereRotation (h * g))
      (sphereRotation_measurePreserving (h * g)) f := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : sphereRotation h ∘ sphereRotation g = sphereRotation (h * g) := by
    funext x
    exact (sphereRotation_mul h g x).symm
  simp only [he]

private theorem sphere_pullback_one (f : SphereSpace) :
    Lp.compMeasurePreserving (sphereRotation 1) (sphereRotation_measurePreserving 1) f = f := by
  have he : sphereRotation 1 = id := funext sphereRotation_one
  simp [he]

/-- Inverse pullback by a rotation is a complex unitary operator on `L²(S²)`. -/
def sphereRotationAction (g : Group) : SphereSpace ≃ₗᵢ[ℂ] SphereSpace :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ (sphereRotation g⁻¹)
      (sphereRotation_measurePreserving g⁻¹))
    (Lp.compMeasurePreservingₗ ℂ (sphereRotation g)
      (sphereRotation_measurePreserving g))
    (by
      ext f : 1
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [sphere_pullback_mul, mul_inv_cancel, sphere_pullback_one])
    (by
      ext f : 1
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [sphere_pullback_mul, inv_mul_cancel, sphere_pullback_one])

/-- The action has the manuscript's natural rotation formula almost everywhere. -/
theorem sphereRotationAction_coeFn (g : Group) (f : SphereSpace) :
    (sphereRotationAction g f : Sphere → ℂ) =ᵐ[sphereMeasure]
      fun x => f (sphereRotation g⁻¹ x) :=
  Lp.coeFn_compMeasurePreserving f (sphereRotation_measurePreserving g⁻¹)

@[simp] theorem sphereRotationAction_one (f : SphereSpace) : sphereRotationAction 1 f = f := by
  change Lp.compMeasurePreserving _ _ f = f
  simpa only [inv_one] using sphere_pullback_one f

/-- The inverse in the pullback gives the usual left representation law. -/
theorem sphereRotationAction_mul (g h : Group) (f : SphereSpace) :
    sphereRotationAction (g * h) f = sphereRotationAction g (sphereRotationAction h f) := by
  change Lp.compMeasurePreserving _ _ f =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
  rw [sphere_pullback_mul]
  simp only [_root_.mul_inv_rev]

/-- The natural unitary SO(3) representation on the sphere used in Section 4. -/
def sphereRepresentation : Group →* SphereSpace ≃ₗᵢ[ℂ] SphereSpace where
  toFun := sphereRotationAction
  map_one' := by ext f : 1; exact sphereRotationAction_one f
  map_mul' g h := by ext f : 1; exact sphereRotationAction_mul g h f

private def sphereInverseContinuousMap (g : Group) : C(Sphere, Sphere) :=
  ⟨sphereRotation g⁻¹, by
    apply Continuous.subtype_mk
    exact (rotationEquiv g⁻¹).continuous.comp continuous_subtype_val⟩

private theorem continuous_sphereInverseContinuousMap : Continuous sphereInverseContinuousMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Group × Sphere => sphereRotation p.1⁻¹ p.2)
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  change Continuous (fun p : Group × Sphere => ∑ j, p.1⁻¹.val i j * (p.2 : SphereAmbient) j)
  apply continuous_finsetSum
  intro j _
  exact (((continuous_subtype_val.comp continuous_inv).comp continuous_fst).matrix_elem i j).mul
    ((PiLp.continuous_apply 2 _ j).comp (continuous_subtype_val.comp continuous_snd))

/-- Every L² orbit is continuous: the natural rotation representation is strongly continuous. -/
theorem continuous_sphereRepresentation_orbit (f : SphereSpace) :
    Continuous (fun g => sphereRepresentation g f) :=
  continuous_const.compMeasurePreservingLp continuous_sphereInverseContinuousMap
    (fun g => sphereRotation_measurePreserving g⁻¹) (by norm_num)

end
end GaussianTesting.SO3
