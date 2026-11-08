module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SO3AngularMomentum
public import GaussianTesting.Kac.SO3AxisSubgroups
public import GaussianTesting.Kac.SO3Cyclic
public import GaussianTesting.Kac.SO3Euler

@[expose] public section

/-!
# The infinitesimal generators of a finite-dimensional SO(3) representation

Strong continuity first gives the bounded skew-adjoint generators of the
three one-parameter axis actions. Differentiating the explicit local Euler
factorization of a conjugated rotation proves their commutator relations.
The Hermitian generators `Jₐ = i Dₐ` therefore form the `AngularMomentum`
triple used in the finite-dimensional Kac estimate. Its kernels are exactly
the fixed spaces of the coordinate-axis subgroups in Eq. (4.1).
-/

namespace GaussianTesting.SO3

open Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 600000

private theorem represented_axis_conjugation
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (ρ : Group →* A) {Dx Dy Dz : A}
    (hx : HasDerivAt (fun t => ρ (rotX t)) Dx 0)
    (hy : HasDerivAt (fun t => ρ (rotY t)) Dy 0)
    (hz : HasDerivAt (fun t => ρ (rotZ t)) Dz 0) (s : ℝ) :
    ρ (rotX s) * Dy * ρ (rotX (-s)) = Real.cos s • Dy + Real.sin s • Dz := by
  have hfactor : ∀ᶠ t in 𝓝 (0 : ℝ),
      ρ (rotX s) * ρ (rotY t) * ρ (rotX (-s)) =
        ρ (rotX (conjugationEulerX s t)) * ρ (rotY (conjugationEulerY s t)) *
          ρ (rotZ (conjugationEulerZ s t)) := by
    filter_upwards [eventually_rotX_rotY_conjugation_factorization s] with t ht
    simpa only [map_mul] using congrArg ρ ht
  simpa only [zero_smul, zero_add] using
    oneParameter_conjugation_generator_of_local_factorization
      (show ρ (rotX 0) = 1 by simp) (show ρ (rotY 0) = 1 by simp)
      (show ρ (rotZ 0) = 1 by simp) hx hy hz s
      (conjugationEulerX_zero s) (conjugationEulerY_zero s) (conjugationEulerZ_zero s)
      (hasDerivAt_conjugationEulerX_zero s) (hasDerivAt_conjugationEulerY_zero s)
      (hasDerivAt_conjugationEulerZ_zero s) hfactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private def representationOperator (π : Group →* E ≃ₗᵢ[ℂ] E) :
    Group →* E →L[ℂ] E where
  toFun g := (π g).toLinearIsometry.toContinuousLinearMap
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

/-- Every strongly continuous finite-dimensional unitary representation of
SO(3) supplies a Hermitian angular-momentum triple. The three kernels are
exactly the subgroup-fixed spaces used in the manuscript's Kac operator. -/
theorem exists_angularMomentum [FiniteDimensional ℂ E] [CompleteSpace E]
    (π : Group →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ v, Continuous (fun g => π g v)) :
    ∃ J : AngularMomentum E,
      UnitaryRepresentation.fixedSubspace π (axisSubgroups 0) = LinearMap.ker J.Jx ∧
      UnitaryRepresentation.fixedSubspace π (axisSubgroups 1) = LinearMap.ker J.Jy ∧
      UnitaryRepresentation.fixedSubspace π (axisSubgroups 2) = LinearMap.ker J.Jz := by
  obtain ⟨Dx, hDx, hskewx, hfixx⟩ := finiteDimensional_unitary_oneParameter_exists_generator
    (fun t => π (rotX t)) (fun v => (hπ v).comp continuous_rotX)
    (by simp) (by intro s t; rw [rotX_add, map_mul])
  obtain ⟨Dy, hDy, hskewy, hfixy⟩ := finiteDimensional_unitary_oneParameter_exists_generator
    (fun t => π (rotY t)) (fun v => (hπ v).comp continuous_rotY)
    (by simp) (by intro s t; rw [rotY_add, map_mul])
  obtain ⟨Dz, hDz, hskewz, hfixz⟩ := finiteDimensional_unitary_oneParameter_exists_generator
    (fun t => π (rotZ t)) (fun v => (hπ v).comp continuous_rotZ)
    (by simp) (by intro s t; rw [rotZ_add, map_mul])
  let ρ := representationOperator π
  have hx0 : HasDerivAt (fun t => ρ (rotX t)) Dx 0 := by
    have h : HasDerivAt (fun t => ρ (rotX t)) (ρ (rotX 0) * Dx) 0 := hDx 0
    simpa using h
  have hy0 : HasDerivAt (fun t => ρ (rotY t)) Dy 0 := by
    have h : HasDerivAt (fun t => ρ (rotY t)) (ρ (rotY 0) * Dy) 0 := hDy 0
    simpa using h
  have hz0 : HasDerivAt (fun t => ρ (rotZ t)) Dz 0 := by
    have h : HasDerivAt (fun t => ρ (rotZ t)) (ρ (rotZ 0) * Dz) 0 := hDz 0
    simpa using h
  have hxy : Dx * Dy - Dy * Dx = Dz :=
    oneParameter_rotationLaw_commutator (show ρ (rotX 0) = 1 by simp) hDx
      (represented_axis_conjugation ρ hx0 hy0 hz0)
  have hyzlaw (s : ℝ) : ρ (rotY s) * Dz * ρ (rotY (-s)) =
      Real.cos s • Dz + Real.sin s • Dx := by
    simpa using represented_axis_conjugation (ρ.comp cycleConj.toMonoidHom)
      (by simpa using hy0) (by simpa using hz0) (by simpa using hx0) s
  have hyz : Dy * Dz - Dz * Dy = Dx :=
    oneParameter_rotationLaw_commutator (show ρ (rotY 0) = 1 by simp) hDy hyzlaw
  have hzxlaw (s : ℝ) : ρ (rotZ s) * Dx * ρ (rotZ (-s)) =
      Real.cos s • Dx + Real.sin s • Dy := by
    simpa using represented_axis_conjugation
      ((ρ.comp cycleConj.toMonoidHom).comp cycleConj.toMonoidHom)
      (by simpa using hz0) (by simpa using hx0) (by simpa using hy0) s
  have hzx : Dz * Dx - Dx * Dz = Dy :=
    oneParameter_rotationLaw_commutator (show ρ (rotZ 0) = 1 by simp) hDz hzxlaw
  let J := angularMomentumOfSkewGenerators Dx Dy Dz hskewx hskewy hskewz hxy hyz hzx
  refine ⟨J, ?_, ?_, ?_⟩
  · change UnitaryRepresentation.fixedSubspace π (axisSubgroups 0) =
      LinearMap.ker (Complex.I • Dx.toLinearMap)
    rw [imaginary_smul_generator_ker]
    ext v
    exact (mem_fixedSubspace_axisX π v).trans (hfixx v)
  · change UnitaryRepresentation.fixedSubspace π (axisSubgroups 1) =
      LinearMap.ker (Complex.I • Dy.toLinearMap)
    rw [imaginary_smul_generator_ker]
    ext v
    exact (mem_fixedSubspace_axisY π v).trans (hfixy v)
  · change UnitaryRepresentation.fixedSubspace π (axisSubgroups 2) =
      LinearMap.ker (Complex.I • Dz.toLinearMap)
    rw [imaginary_smul_generator_ker]
    ext v
    exact (mem_fixedSubspace_axisZ π v).trans (hfixz v)

end
end GaussianTesting.SO3
