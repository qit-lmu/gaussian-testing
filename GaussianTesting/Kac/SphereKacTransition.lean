module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereRepresentation
public import GaussianTesting.Kac.GeneralRepresentation
public import GaussianTesting.Kac.AxisAverage
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# The spherical Kac transition operator

The transition described in Section 4 chooses one coordinate axis uniformly
and then rotates by a uniform angle in a full circle. We define its action
on continuous observables by ordinary angular integrals, and identify the
unique bounded extension to `L²(S²)` with the average of the three
axis-invariant projections. The representation acts by inverse pullback;
reflection of the full-period integral supplies the usual forward-rotation
formula for the transition.
-/

namespace GaussianTesting.SO3

open MeasureTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 800000

/-- Regard a continuous observable on the sphere as an element of its L² space. -/
abbrev sphereContinuousToLp : C(Sphere, ℂ) →L[ℂ] SphereSpace :=
  ContinuousMap.toLp 2 sphereMeasure ℂ

/-- The inverse-pullback action on continuous sphere observables. -/
def sphereContinuousRotation (g : Group) (f : C(Sphere, ℂ)) : C(Sphere, ℂ) :=
  ⟨fun x => f (sphereRotation g⁻¹ x), f.continuous.comp (by
    apply Continuous.subtype_mk
    exact (rotationEquiv g⁻¹).continuous.comp continuous_subtype_val)⟩

@[simp] theorem sphereContinuousRotation_apply (g : Group) (f : C(Sphere, ℂ))
    (x : Sphere) : sphereContinuousRotation g f x = f (sphereRotation g⁻¹ x) := rfl

/-- A continuous observable has a continuous orbit in the uniform norm. -/
theorem continuous_sphereContinuousRotation (f : C(Sphere, ℂ)) :
    Continuous (fun g => sphereContinuousRotation g f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Group × Sphere => f (sphereRotation p.1⁻¹ p.2))
  apply f.continuous.comp
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  change Continuous (fun p : Group × Sphere =>
    ∑ j, p.1⁻¹.val i j * (p.2 : SphereAmbient) j)
  apply continuous_finsetSum
  intro j _
  exact (((continuous_subtype_val.comp continuous_inv).comp continuous_fst).matrix_elem i j).mul
    ((PiLp.continuous_apply 2 _ j).comp (continuous_subtype_val.comp continuous_snd))

/-- The continuous-observable action agrees with the unitary L² action. -/
theorem sphereContinuousToLp_rotation (g : Group) (f : C(Sphere, ℂ)) :
    sphereContinuousToLp (sphereContinuousRotation g f) =
      sphereRepresentation g (sphereContinuousToLp f) := by
  apply Lp.ext
  have hf := (sphereRotation_measurePreserving g⁻¹).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sphereMeasure f)
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sphereMeasure
      (sphereContinuousRotation g f),
    sphereRotationAction_coeFn g (sphereContinuousToLp f), hf] with x hx hrot hfx
  exact hx.trans (hrot.trans hfx).symm

/-- Continuous sphere observables form a dense subspace of the sphere's L² space. -/
theorem sphereContinuousToLp_denseRange : DenseRange sphereContinuousToLp :=
  ContinuousMap.toLp_denseRange ℂ sphereMeasure ℂ (by norm_num)

/-- Uniform averaging about one axis, acting on continuous sphere observables. -/
def sphereAxisContinuousAverage (a : Fin 3) (f : C(Sphere, ℂ)) : C(Sphere, ℂ) :=
  ((2 * Real.pi)⁻¹ : ℝ) •
    ∫ θ in 0..2 * Real.pi, sphereContinuousRotation (axisRotation a θ) f

private theorem continuous_axisContinuousOrbit (a : Fin 3) (f : C(Sphere, ℂ)) :
    Continuous (fun θ => sphereContinuousRotation (axisRotation a θ) f) :=
  (continuous_sphereContinuousRotation f).comp (continuous_axisRotation a)

private theorem sphereAxisContinuousAverage_apply_inverse (a : Fin 3)
    (f : C(Sphere, ℂ)) (x : Sphere) :
    sphereAxisContinuousAverage a f x = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ θ in 0..2 * Real.pi, f (sphereRotation (axisRotation a θ)⁻¹ x) := by
  change ((2 * Real.pi)⁻¹ : ℝ) •
    ((∫ θ in 0..2 * Real.pi, sphereContinuousRotation (axisRotation a θ) f) x) = _
  congr 1
  exact ((ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm
    (μ := volume) ((continuous_axisContinuousOrbit a f).intervalIntegrable _ _)).symm

/-- Reflection of a full uniform circle changes inverse rotations to forward rotations. -/
theorem sphere_axisIntegral_inverse_eq (a : Fin 3) (f : C(Sphere, ℂ)) (x : Sphere) :
    (∫ θ in 0..2 * Real.pi, f (sphereRotation (axisRotation a θ)⁻¹ x)) =
      ∫ θ in 0..2 * Real.pi, f (sphereRotation (axisRotation a θ) x) := by
  have hp : Function.Periodic (fun θ => f (sphereRotation (axisRotation a θ) x))
      (2 * Real.pi) := by
    intro θ
    change f (sphereRotation (axisRotation a (θ + 2 * Real.pi)) x) = _
    rw [axisRotation_periodic]
  simp_rw [← axisRotation_neg]
  exact (intervalIntegral.integral_comp_neg
    (fun θ => f (sphereRotation (axisRotation a θ) x))).trans (by
      simpa only [neg_zero, neg_add_cancel, zero_add] using
        hp.intervalIntegral_add_eq (-(2 * Real.pi)) 0)

/-- The ordinary uniform-angle formula for the axis transition, at every sphere point. -/
theorem sphereAxisContinuousAverage_apply (a : Fin 3) (f : C(Sphere, ℂ)) (x : Sphere) :
    sphereAxisContinuousAverage a f x = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ θ in 0..2 * Real.pi, f (sphereRotation (axisRotation a θ) x) := by
  rw [sphereAxisContinuousAverage_apply_inverse, sphere_axisIntegral_inverse_eq]

/-- The continuous axis average becomes the Hilbert-space Bochner average in L². -/
theorem sphereContinuousToLp_axisAverage (a : Fin 3) (f : C(Sphere, ℂ)) :
    sphereContinuousToLp (sphereAxisContinuousAverage a f) =
      axisCircleAverage sphereRepresentation a (sphereContinuousToLp f) := by
  let L := sphereContinuousToLp.restrictScalars ℝ
  change L (((2 * Real.pi)⁻¹ : ℝ) • _) = _
  rw [map_smul, ← L.intervalIntegral_comp_comm
    ((continuous_axisContinuousOrbit a f).intervalIntegrable _ _)]
  change ((2 * Real.pi)⁻¹ : ℝ) •
    (∫ θ in 0..2 * Real.pi, sphereContinuousToLp
      (sphereContinuousRotation (axisRotation a θ) f)) = _
  simp only [sphereContinuousToLp_rotation, axisCircleAverage]
  rfl

/-- One step of the spherical Kac walk on continuous observables: uniform axis,
followed by a uniform angle about that axis. -/
def sphereContinuousTransition (f : C(Sphere, ℂ)) : C(Sphere, ℂ) :=
  (3 : ℂ)⁻¹ • (sphereAxisContinuousAverage 0 f + sphereAxisContinuousAverage 1 f +
    sphereAxisContinuousAverage 2 f)

/-- The classical Kac transition formula on continuous observables. -/
theorem sphereContinuousTransition_apply (f : C(Sphere, ℂ)) (x : Sphere) :
    sphereContinuousTransition f x = (3 : ℂ)⁻¹ •
      ∑ a : Fin 3, ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ θ in 0..2 * Real.pi, f (sphereRotation (axisRotation a θ) x) := by
  change (3 : ℂ)⁻¹ • (sphereAxisContinuousAverage 0 f x +
    sphereAxisContinuousAverage 1 f x + sphereAxisContinuousAverage 2 f x) = _
  simp only [Fin.sum_univ_three, sphereAxisContinuousAverage_apply]

/-- The spherical Kac transition on all of L², defined by the three normalized
vector-valued angular integrals. -/
def sphereKacTransition : SphereSpace →L[ℂ] SphereSpace :=
  (3 : ℂ)⁻¹ •
    (axisCircleAverageCLM sphereRepresentation continuous_sphereRepresentation_orbit 0 +
      axisCircleAverageCLM sphereRepresentation continuous_sphereRepresentation_orbit 1 +
      axisCircleAverageCLM sphereRepresentation continuous_sphereRepresentation_orbit 2)

/-- On every L² vector the transition is the average of its three Bochner circle integrals. -/
theorem sphereKacTransition_apply (f : SphereSpace) :
    sphereKacTransition f = (3 : ℂ)⁻¹ •
      ∑ a : Fin 3, ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ θ in 0..2 * Real.pi, sphereRepresentation (axisRotation a θ) f := by
  simp only [sphereKacTransition, Fin.sum_univ_three, smul_apply, add_apply]
  rfl

/-- The integral-defined spherical transition is precisely the average of the
three axis-invariant orthogonal projections used in Section 4. -/
theorem sphereKacTransition_eq_kacAverage :
    sphereKacTransition = kacAverage sphereRepresentation := by
  simp only [sphereKacTransition, kacAverage, UnitaryRepresentation.groupKacAverage,
    axisCircleAverageCLM_eq_fixedProjection]

/-- The L² transition extends the pointwise classical transition on continuous observables. -/
theorem sphereKacTransition_continuous (f : C(Sphere, ℂ)) :
    sphereKacTransition (sphereContinuousToLp f) =
      sphereContinuousToLp (sphereContinuousTransition f) := by
  simp only [sphereKacTransition, sphereContinuousTransition, map_smul, map_add,
    smul_apply, add_apply,
    sphereContinuousToLp_axisAverage]
  rfl

/-- Density of continuous observables characterizes the Kac transition uniquely
among bounded complex-linear operators on L². -/
theorem sphereKacTransition_unique (T : SphereSpace →L[ℂ] SphereSpace)
    (hT : ∀ f : C(Sphere, ℂ), T (sphereContinuousToLp f) =
      sphereContinuousToLp (sphereContinuousTransition f)) :
    T = sphereKacTransition := by
  apply DFunLike.coe_injective
  apply sphereContinuousToLp_denseRange.equalizer T.continuous sphereKacTransition.continuous
  funext f
  exact (hT f).trans (sphereKacTransition_continuous f).symm

end
end GaussianTesting.SO3
