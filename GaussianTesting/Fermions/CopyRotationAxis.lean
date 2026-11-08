module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CopyCoordinates
public import GaussianTesting.Fermions.CopyRotationDerivative

@[expose] public section

/-!
# The axis generators and fixed spaces in Theorem 5.2

For the manuscript's second-quantized copy action, Majorana covariance and the
fixed vacuum identify the axis derivatives with `i L_23/2`, `-i L_13/2`, and
`i L_12/2`. Their kernels are exactly the three pair-test ranges, proving
`S = T_π` with the usual coordinate-axis convention.
-/

namespace GaussianTesting

open Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {m : ℕ}

/-- The SO(3) column action on the three sets of Majoranas. -/
def HasFermionCopyMajoranaAction
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m)) : Prop :=
  ∀ (R : SO3.Group) (r : Fin 3) (a : Fin m × Bool) (v : H3 (Qm m)),
    π R (fermionCubeMajorana r a v) =
      ∑ s, (R.val s r : ℂ) • fermionCubeMajorana s a (π R v)

/-- The derivatives have the manuscript's generators with the standard-angle
normalization and coordinate-axis orientations. -/
theorem fermion_copyRepresentation_axis_derivatives
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m))
    (hπ : ∀ v, Continuous (fun g => π g v))
    (hc : HasFermionCopyMajoranaAction π)
    (hv : ∀ R, π R (fermionTripleVacuum m) = fermionTripleVacuum m) :
    (∀ v, HasDerivAt (fun t => π (SO3.rotX t) v) (fermionCopyGenerator 1 2 v) 0) ∧
    (∀ v, HasDerivAt (fun t => π (SO3.rotY t) v) (-fermionCopyGenerator 0 2 v) 0) ∧
    (∀ v, HasDerivAt (fun t => π (SO3.rotZ t) v) (fermionCopyGenerator 0 1 v) 0) := by
  have hcomm (A : H3 (Qm m) →ₗ[ℂ] H3 (Qm m))
      (hA : ∀ r a, A * fermionCubeMajorana r a = fermionCubeMajorana r a * A) :
      ∃ z : ℂ, A = z • LinearMap.id := by
    apply exists_scalar_of_commutes_fermionCubeMajorana
    intro r a v
    exact congrArg (fun T : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) => T v) (hA r a)
  have hx0 : SO3.rotXMatrix 0 = 1 :=
    congrArg (fun R : SO3.Group => R.val) SO3.rotX_zero
  have hy0 : SO3.rotYMatrix 0 = 1 :=
    congrArg (fun R : SO3.Group => R.val) SO3.rotY_zero
  have hz0 : SO3.rotZMatrix 0 = 1 :=
    congrArg (fun R : SO3.Group => R.val) SO3.rotZ_zero
  have hxK (r s : Fin 3) : HasDerivAt (fun t => SO3.rotXMatrix t r s)
      (!![0, 0, 0; 0, 0, -1; 0, 1, 0] r s) 0 := by
    fin_cases r <;> fin_cases s <;> dsimp only [SO3.rotXMatrix]
    all_goals first
      | exact hasDerivAt_const 0 _
      | simpa using Real.hasDerivAt_cos 0
      | simpa using Real.hasDerivAt_sin 0
      | simpa using (Real.hasDerivAt_sin 0).const_mul (-1)
  have hyK (r s : Fin 3) : HasDerivAt (fun t => SO3.rotYMatrix t r s)
      (!![0, 0, 1; 0, 0, 0; -1, 0, 0] r s) 0 := by
    fin_cases r <;> fin_cases s <;> dsimp only [SO3.rotYMatrix]
    all_goals first
      | exact hasDerivAt_const 0 _
      | simpa using Real.hasDerivAt_cos 0
      | simpa using Real.hasDerivAt_sin 0
      | simpa using (Real.hasDerivAt_sin 0).const_mul (-1)
  have hzK (r s : Fin 3) : HasDerivAt (fun t => SO3.rotZMatrix t r s)
      (!![0, -1, 0; 1, 0, 0; 0, 0, 0] r s) 0 := by
    fin_cases r <;> fin_cases s <;> dsimp only [SO3.rotZMatrix]
    all_goals first
      | exact hasDerivAt_const 0 _
      | simpa using Real.hasDerivAt_cos 0
      | simpa using Real.hasDerivAt_sin 0
      | simpa using (Real.hasDerivAt_sin 0).const_mul (-1)
  constructor
  · apply unitary_oneParameter_deriv_of_majorana_covariance
      (fun t => π (SO3.rotX t)) (fun v => (hπ v).comp SO3.continuous_rotX)
      (by simp) (by intro s t; rw [SO3.rotX_add, map_mul])
      fermionCubeMajorana hcomm (fermionTripleVacuum m) (fermionTripleVacuum_ne_zero m)
      (fun t => hv (SO3.rotX t)) SO3.rotXMatrix
      !![0, 0, 0; 0, 0, -1; 0, 1, 0] hx0 hxK
      (fun t r a v => hc (SO3.rotX t) r a v)
      (fermionCopyGenerator 1 2) (fermionCopyGenerator_vacuum.2.1)
    intro r a
    have h := fermionCopyGenerator_comm 1 2 r (by decide) a
    fin_cases r <;> simpa [Fin.sum_univ_succ] using h
  constructor
  · apply unitary_oneParameter_deriv_of_majorana_covariance
      (fun t => π (SO3.rotY t)) (fun v => (hπ v).comp SO3.continuous_rotY)
      (by simp) (by intro s t; rw [SO3.rotY_add, map_mul])
      fermionCubeMajorana hcomm (fermionTripleVacuum m) (fermionTripleVacuum_ne_zero m)
      (fun t => hv (SO3.rotY t)) SO3.rotYMatrix
      !![0, 0, 1; 0, 0, 0; -1, 0, 0] hy0 hyK
      (fun t r a v => hc (SO3.rotY t) r a v)
      (-fermionCopyGenerator 0 2) (by simpa using congrArg Neg.neg fermionCopyGenerator_vacuum.2.2)
    intro r a
    have h := congrArg Neg.neg (fermionCopyGenerator_comm 0 2 r (by decide) a)
    simp only [neg_mul, mul_neg, neg_sub_neg]
    fin_cases r <;> simpa [Fin.sum_univ_succ, neg_sub] using h
  · apply unitary_oneParameter_deriv_of_majorana_covariance
      (fun t => π (SO3.rotZ t)) (fun v => (hπ v).comp SO3.continuous_rotZ)
      (by simp) (by intro s t; rw [SO3.rotZ_add, map_mul])
      fermionCubeMajorana hcomm (fermionTripleVacuum m) (fermionTripleVacuum_ne_zero m)
      (fun t => hv (SO3.rotZ t)) SO3.rotZMatrix
      !![0, -1, 0; 1, 0, 0; 0, 0, 0] hz0 hzK
      (fun t r a v => hc (SO3.rotZ t) r a v)
      (fermionCopyGenerator 0 1) (fermionCopyGenerator_vacuum.1)
    intro r a
    have h := fermionCopyGenerator_comm 0 1 r (by decide) a
    fin_cases r <;> simpa [Fin.sum_univ_succ] using h

/-- The three coordinate-axis fixed spaces are exactly the pair Lambda kernels. -/
theorem fermion_copyRepresentation_axis_fixed
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m))
    (hπ : ∀ v, Continuous (fun g => π g v))
    (hc : HasFermionCopyMajoranaAction π)
    (hv : ∀ R, π R (fermionTripleVacuum m) = fermionTripleVacuum m) :
    UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 0) =
      LinearMap.ker (p23 (lambdaF m)) ∧
    UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 1) =
      LinearMap.ker (p13 (lambdaF m)) ∧
    UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups 2) =
      LinearMap.ker (p12 (lambdaF m)) := by
  obtain ⟨hx, hy, hz⟩ := fermion_copyRepresentation_axis_derivatives π hπ hc hv
  have hi : Complex.I / 2 ≠ 0 := div_ne_zero Complex.I_ne_zero (by norm_num)
  constructor
  · rw [fermion_fixedSubspace_axisX_of_deriv π hπ _ hx,
      fermionCopyGenerator23, LinearMap.ker_smul _ _ hi, ker_Lgen23]
  constructor
  · rw [fermion_fixedSubspace_axisY_of_deriv π hπ (-fermionCopyGenerator 0 2) hy,
      LinearMap.ker_neg, fermionCopyGenerator13, LinearMap.ker_smul _ _ hi, ker_Lgen13]
  · rw [fermion_fixedSubspace_axisZ_of_deriv π hπ _ hz,
      fermionCopyGenerator12, LinearMap.ker_smul _ _ hi, ker_Lgen12]

/-- The equality `S = T_π` in Theorem 5.2 for the second-quantized copy action. -/
theorem fermion_kacAverage_eq_of_majorana_action
    (π : SO3.Group →* H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m))
    (hπ : ∀ v, Continuous (fun g => π g v))
    (hc : HasFermionCopyMajoranaAction π)
    (hv : ∀ R, π R (fermionTripleVacuum m) = fermionTripleVacuum m) :
    (SO3.kacAverage π).toLinearMap = Sop (PF m) := by
  obtain ⟨hx, hy, hz⟩ := fermion_copyRepresentation_axis_fixed π hπ hc hv
  exact fermion_kacAverage_eq_Sop_of_axis_fixed π hx hy hz

end
end GaussianTesting
