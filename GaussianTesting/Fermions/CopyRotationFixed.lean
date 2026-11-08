module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.SO3Bridge
public import GaussianTesting.Kac.GeneralRepresentation

@[expose] public section

/-!
# Axis-fixed subspaces for the fermionic copy action

Theorem 5.2 identifies each pair-test projection with the fixed space of a
coordinate-axis subgroup. These helpers perform that identification from the
infinitesimal action at angle zero, including the irrelevant nonzero scalar
normalization of the generators.
-/

namespace GaussianTesting

noncomputable section

section OneParameter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A continuous unitary one-parameter action is fixed exactly on the kernel
of its vector derivative at zero. -/
theorem unitary_oneParameter_fixed_iff_of_deriv_zero
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (hcont : ∀ v, Continuous (fun t => U t v))
    (hzero : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (T : E →ₗ[ℂ] E)
    (hT : ∀ v, HasDerivAt (fun t => U t v) (T v) 0) (v : E) :
    (∀ t, U t v = v) ↔ T v = 0 := by
  obtain ⟨D, hD, _, hfix⟩ := finiteDimensional_unitary_oneParameter_exists_generator
    U hcont hzero hadd
  have hdv := oneParameter_generator_hasDerivAt_apply hD 0 v
  have he : T v = D v := by
    have h := (hT v).unique hdv
    simpa [hzero] using h
  exact (hfix v).trans (by rw [he])

end OneParameter

variable {m : ℕ}

/-- The first-axis fixed space is the kernel of the derivative on copies 2,3. -/
theorem fermion_fixedSubspace_axisX_of_deriv
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m))
    (hπ : ∀ v, Continuous (fun g => π g v))
    (T : H3 (Qm m) →ₗ[ℂ] H3 (Qm m))
    (hT : ∀ v, HasDerivAt (fun t => π (SO3.rotX t) v) (T v) 0) :
    UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 0) = LinearMap.ker T := by
  ext v
  exact (SO3.mem_fixedSubspace_axisX π v).trans
    (unitary_oneParameter_fixed_iff_of_deriv_zero (fun t => π (SO3.rotX t))
      (fun v => (hπ v).comp SO3.continuous_rotX) (by simp)
      (by intro s t; rw [SO3.rotX_add, map_mul]) T hT v)

/-- The second-axis fixed space is the kernel of the derivative on copies 1,3. -/
theorem fermion_fixedSubspace_axisY_of_deriv
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m))
    (hπ : ∀ v, Continuous (fun g => π g v))
    (T : H3 (Qm m) →ₗ[ℂ] H3 (Qm m))
    (hT : ∀ v, HasDerivAt (fun t => π (SO3.rotY t) v) (T v) 0) :
    UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 1) = LinearMap.ker T := by
  ext v
  exact (SO3.mem_fixedSubspace_axisY π v).trans
    (unitary_oneParameter_fixed_iff_of_deriv_zero (fun t => π (SO3.rotY t))
      (fun v => (hπ v).comp SO3.continuous_rotY) (by simp)
      (by intro s t; rw [SO3.rotY_add, map_mul]) T hT v)

/-- The third-axis fixed space is the kernel of the derivative on copies 1,2. -/
theorem fermion_fixedSubspace_axisZ_of_deriv
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m))
    (hπ : ∀ v, Continuous (fun g => π g v))
    (T : H3 (Qm m) →ₗ[ℂ] H3 (Qm m))
    (hT : ∀ v, HasDerivAt (fun t => π (SO3.rotZ t) v) (T v) 0) :
    UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 2) = LinearMap.ker T := by
  ext v
  exact (SO3.mem_fixedSubspace_axisZ π v).trans
    (unitary_oneParameter_fixed_iff_of_deriv_zero (fun t => π (SO3.rotZ t))
      (fun v => (hπ v).comp SO3.continuous_rotZ) (by simp)
      (by intro s t; rw [SO3.rotZ_add, map_mul]) T hT v)

/-- The pair-projection average is the Kac operator once the three axis-fixed
spaces have been identified, in the order X=23, Y=13, Z=12. -/
theorem fermion_kacAverage_eq_Sop_of_axis_fixed
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m))
    (hx : UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 0) =
      LinearMap.ker (p23 (lambdaF m)))
    (hy : UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 1) =
      LinearMap.ker (p13 (lambdaF m)))
    (hz : UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 2) =
      LinearMap.ker (p12 (lambdaF m))) :
    (SO3.kacAverage π).toLinearMap = Sop (PF m) := by
  simp only [SO3.kacAverage, UnitaryRepresentation.groupKacAverage, hx, hy, hz]
  change (3 : ℂ)⁻¹ •
    ((LinearMap.ker (p23 (lambdaF m))).starProjection.toLinearMap +
      (LinearMap.ker (p13 (lambdaF m))).starProjection.toLinearMap +
      (LinearMap.ker (p12 (lambdaF m))).starProjection.toLinearMap) = _
  rw [← p23_PF, ← p13_PF, ← p12_PF]
  simp only [Sop]
  congr 1
  abel

end
end GaussianTesting
