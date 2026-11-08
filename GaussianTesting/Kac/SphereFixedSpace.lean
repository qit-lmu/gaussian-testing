module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereKacTransition
public import GaussianTesting.Kac.SphereTransitivity
public import GaussianTesting.Kac.KacFixedSpace
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-!
# Constants as the fixed space of the spherical Kac operator

In the proof of Theorem 4.1 the trivial representation consists of constants.
Fixedness under the average of the axis projections implies invariance under
all rotations. Transitivity makes the Haar average of any continuous sphere
observable constant; continuity and density extend this to L². Consequently
an invariant L² vector is constant almost everywhere.
-/

namespace GaussianTesting.SO3

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The constant function with value `c`, as an L² vector on the sphere. -/
def sphereConstant (c : ℂ) : SphereSpace :=
  sphereContinuousToLp (ContinuousMap.const Sphere c)

/-- Constant L² functions form the span of the constant one function. -/
def sphereConstants : Submodule ℂ SphereSpace :=
  Submodule.span ℂ {sphereConstant 1}

@[simp] theorem sphereConstant_smul_one (c : ℂ) : c • sphereConstant 1 = sphereConstant c := by
  unfold sphereConstant
  rw [← map_smul]
  congr 1
  ext x
  simp

/-- Membership in the constant subspace means equality to a literal constant L² function. -/
theorem mem_sphereConstants (f : SphereSpace) :
    f ∈ sphereConstants ↔ ∃ c : ℂ, f = sphereConstant c := by
  simp only [sphereConstants, Submodule.mem_span_singleton, sphereConstant_smul_one, eq_comm]

/-- Constant sphere functions have a closed range in L². -/
theorem sphereConstants_isClosed : IsClosed (sphereConstants : Set SphereSpace) := by
  exact (Submodule.span ℂ {sphereConstant 1}).closed_of_finiteDimensional

/-- The representative of a constant L² function is almost everywhere that constant. -/
theorem sphereConstant_coeFn (c : ℂ) :
    (sphereConstant c : Sphere → ℂ) =ᵐ[sphereMeasure] fun _ => c :=
  ContinuousMap.coeFn_toLp sphereMeasure (ContinuousMap.const Sphere c)

/-- Every constant function is fixed by every rotation. -/
theorem sphereRepresentation_constant (g : Group) (c : ℂ) :
    sphereRepresentation g (sphereConstant c) = sphereConstant c := by
  rw [sphereConstant, ← sphereContinuousToLp_rotation]
  rfl

private abbrev rotationHaar : Measure Group := UnitaryRepresentation.probabilityHaar

private theorem integrable_sphereOrbit (f : SphereSpace) :
    Integrable (fun g => sphereRepresentation g f) rotationHaar :=
  (continuous_sphereRepresentation_orbit f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Normalized Haar averaging of L² vectors. Only vector-orbit continuity is used. -/
private def sphereHaarAverage : SphereSpace →L[ℂ] SphereSpace :=
  ({ toFun := fun f => ∫ g, sphereRepresentation g f ∂rotationHaar
     map_add' := fun f h => by
       simp only [map_add]
       exact integral_add (integrable_sphereOrbit f) (integrable_sphereOrbit h)
     map_smul' := fun c f => by
       simp only [map_smul, RingHom.id_apply]
       exact integral_smul c _ } : SphereSpace →ₗ[ℂ] SphereSpace).mkContinuous 1 (by
    intro f
    simpa using norm_integral_le_of_norm_le_const (μ := rotationHaar)
      (Filter.Eventually.of_forall fun g => le_of_eq ((sphereRepresentation g).norm_map f)))

private theorem integrable_sphereContinuousOrbit (f : C(Sphere, ℂ)) :
    Integrable (fun g => sphereContinuousRotation g f) rotationHaar :=
  (continuous_sphereContinuousRotation f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private def sphereContinuousHaarAverage (f : C(Sphere, ℂ)) : C(Sphere, ℂ) :=
  ∫ g, sphereContinuousRotation g f ∂rotationHaar

private theorem sphereContinuousHaarAverage_apply (f : C(Sphere, ℂ)) (x : Sphere) :
    sphereContinuousHaarAverage f x =
      ∫ g, f (sphereRotation g⁻¹ x) ∂rotationHaar :=
  ((ContinuousMap.evalCLM ℝ x).integral_comp_comm
    (integrable_sphereContinuousOrbit f)).symm

private theorem sphereHaarAverage_continuous (f : C(Sphere, ℂ)) :
    sphereHaarAverage (sphereContinuousToLp f) =
      sphereContinuousToLp (sphereContinuousHaarAverage f) := by
  change (∫ g, sphereRepresentation g (sphereContinuousToLp f) ∂rotationHaar) = _
  simp_rw [← sphereContinuousToLp_rotation]
  exact sphereContinuousToLp.integral_comp_comm (integrable_sphereContinuousOrbit f)

private theorem sphereContinuousHaarAverage_constant (f : C(Sphere, ℂ)) (x y : Sphere) :
    sphereContinuousHaarAverage f y = sphereContinuousHaarAverage f x := by
  obtain ⟨h, rfl⟩ := sphereRotation_transitive x y
  rw [sphereContinuousHaarAverage_apply, sphereContinuousHaarAverage_apply]
  calc
    _ = ∫ g, f (sphereRotation (h⁻¹ * g)⁻¹ x) ∂rotationHaar := by
      simp only [mul_inv_rev, inv_inv, sphereRotation_mul]
    _ = _ := integral_mul_left_eq_self (μ := rotationHaar)
      (fun g : Group => f (sphereRotation g⁻¹ x)) h⁻¹

private theorem sphereHaarAverage_mem_constants (v : SphereSpace) :
    sphereHaarAverage v ∈ sphereConstants := by
  refine sphereContinuousToLp_denseRange.induction_on
    (p := fun w => sphereHaarAverage w ∈ sphereConstants) v
    (sphereConstants_isClosed.preimage sphereHaarAverage.continuous) ?_
  intro f
  rw [sphereHaarAverage_continuous, mem_sphereConstants]
  refine ⟨sphereContinuousHaarAverage f spherePole, ?_⟩
  unfold sphereConstant
  congr 1
  ext x
  exact sphereContinuousHaarAverage_constant f spherePole x

/-- The SO(3)-invariant vectors in spherical L² are precisely the constant functions.
The proof uses transitivity on continuous observables and then L² density. -/
theorem sphereRepresentation_invariant_iff_constant (f : SphereSpace) :
    (∀ g : Group, sphereRepresentation g f = f) ↔ ∃ c : ℂ, f = sphereConstant c := by
  constructor
  · intro hf
    have he : sphereHaarAverage f = f :=
      integral_eq_const (Filter.Eventually.of_forall hf)
    exact (mem_sphereConstants f).mp (he ▸ sphereHaarAverage_mem_constants f)
  · rintro ⟨c, rfl⟩ g
    exact sphereRepresentation_constant g c

/-- In Theorem 4.1, the spherical Kac operator fixes exactly the constant L² functions. -/
theorem sphereKacTransition_eq_self_iff_constant (f : SphereSpace) :
    sphereKacTransition f = f ↔ ∃ c : ℂ, f = sphereConstant c := by
  rw [sphereKacTransition_eq_kacAverage, kacAverage_eq_self_iff_invariant,
    sphereRepresentation_invariant_iff_constant]

/-- The fixed-space characterization expressed directly on measurable representatives. -/
theorem sphereKacTransition_eq_self_iff_ae_constant (f : SphereSpace) :
    sphereKacTransition f = f ↔ ∃ c : ℂ, (f : Sphere → ℂ) =ᵐ[sphereMeasure] fun _ => c := by
  rw [sphereKacTransition_eq_self_iff_constant]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, sphereConstant_coeFn c⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Lp.ext (hc.trans (sphereConstant_coeFn c).symm)⟩

/-- The eigenvalue-one eigenspace is the subspace of constant functions. -/
theorem sphereKacTransition_fixedSpace :
    Module.End.eigenspace sphereKacTransition.toLinearMap 1 = sphereConstants := by
  ext f
  rw [Module.End.mem_eigenspace_iff, one_smul, mem_sphereConstants]
  exact sphereKacTransition_eq_self_iff_constant f

end
end GaussianTesting.SO3
