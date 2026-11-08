module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.OccupationVacuum
public import GaussianTesting.Fermions.SecondQuantization
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

@[expose] public section

/-!
# Exterior Fock space in occupation coordinates

The exterior algebra acts by creation operators; evaluation at the vacuum
identifies its ordered wedge basis with the occupation basis. This is the
identification used for the second-quantized copy action in Section 5.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- The creation operators anticommute, including nilpotence when the modes agree. -/
theorem fermionCreation_anticomm (k l : Fin m) :
    fermionCreation k ∘ₗ fermionCreation l +
      fermionCreation l ∘ₗ fermionCreation k = 0 := by
  by_cases hkl : k = l
  · subst l
    ext ψ x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, PiLp.add_apply,
      fermionCreation_apply, LinearMap.zero_apply, PiLp.zero_apply]
    have hx : flipBit k x k = !x k := by simp [flipBit]
    rw [hx]
    cases x k <;> simp
  · have h00 := maj_anticomm (a := (k, false)) (b := (l, false)) (by simpa using hkl)
    have h01 := maj_anticomm (a := (k, false)) (b := (l, true)) (by simp)
    have h10 := maj_anticomm (a := (k, true)) (b := (l, false)) (by simp)
    have h11 := maj_anticomm (a := (k, true)) (b := (l, true)) (by simpa using hkl)
    unfold fermionCreation
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.sub_comp,
      LinearMap.comp_sub, smul_sub, smul_smul]
    linear_combination (norm := (module_nf; simp [Complex.I_sq])) (1 / 4 : ℂ) • h00 - (Complex.I / 4) • h01 -
      (Complex.I / 4) • h10 - (1 / 4 : ℂ) • h11

/-- Creation by an arbitrary one-particle vector. -/
def fermionCreationLinear : (Fin m → ℂ) →ₗ[ℂ] Module.End ℂ (HF m) where
  toFun v := ∑ k, v k • fermionCreation k
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z v := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem fermionCreationLinear_single (k : Fin m) :
    fermionCreationLinear (Pi.single k (1 : ℂ)) = fermionCreation k := by
  classical
  simp [fermionCreationLinear, Pi.single_apply]

theorem fermionCreationLinear_sq_zero (v : Fin m → ℂ) :
    fermionCreationLinear v * fermionCreationLinear v = 0 := by
  have hexp : fermionCreationLinear v * fermionCreationLinear v =
      ∑ k, ∑ l, (v k * v l) • (fermionCreation k ∘ₗ fermionCreation l) := by
    apply LinearMap.ext
    intro ψ
    simp only [fermionCreationLinear, Module.End.mul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      LinearMap.comp_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hrev : fermionCreationLinear v * fermionCreationLinear v =
      ∑ k, ∑ l, (v k * v l) • (fermionCreation l ∘ₗ fermionCreation k) := by
    rw [hexp, Finset.sum_comm]
    simp only [mul_comm]
  have h : fermionCreationLinear v * fermionCreationLinear v +
      fermionCreationLinear v * fermionCreationLinear v = 0 := by
    conv_lhs => lhs; rw [hexp]
    conv_lhs => rhs; rw [hrev]
    simp only [← Finset.sum_add_distrib, ← smul_add, fermionCreation_anticomm,
      smul_zero, Finset.sum_const_zero]
  linear_combination (norm := module) (1 / 2 : ℂ) • h

/-- The exterior algebra acts on Fock space by creation operators. -/
def fermionExteriorCreation : ExteriorAlgebra ℂ (Fin m → ℂ) →ₐ[ℂ] Module.End ℂ (HF m) :=
  ExteriorAlgebra.lift ℂ ⟨fermionCreationLinear, fermionCreationLinear_sq_zero⟩

@[simp] theorem fermionExteriorCreation_ι (v : Fin m → ℂ) :
    fermionExteriorCreation (ExteriorAlgebra.ι ℂ v) = fermionCreationLinear v := by
  simp [fermionExteriorCreation]

/-- Evaluate the exterior creation action at the vacuum. -/
def fermionExteriorToOccupation : ExteriorAlgebra ℂ (Fin m → ℂ) →ₗ[ℂ] HF m :=
  (LinearMap.applyₗ (fermionVacuum m)) ∘ₗ fermionExteriorCreation.toLinearMap

@[simp] theorem fermionExteriorToOccupation_one :
    fermionExteriorToOccupation (1 : ExteriorAlgebra ℂ (Fin m → ℂ)) = fermionVacuum m := by
  simp [fermionExteriorToOccupation]

theorem fermionExteriorToOccupation_ι_mul (v : Fin m → ℂ)
    (x : ExteriorAlgebra ℂ (Fin m → ℂ)) :
    fermionExteriorToOccupation (ExteriorAlgebra.ι ℂ v * x) =
      fermionCreationLinear v (fermionExteriorToOccupation x) := by
  simp [fermionExteriorToOccupation, Module.End.mul_apply]

private theorem fermionExteriorToOccupation_basis_word (l : List (Fin m)) :
    fermionExteriorToOccupation
      ((l.map fun k => ExteriorAlgebra.ι ℂ (Pi.single k (1 : ℂ))).prod) =
      fermionCreationWord l := by
  induction l with
  | nil => simp [fermionCreationWord]
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons, fermionExteriorToOccupation_ι_mul,
      fermionCreationLinear_single, ih]
    rfl

/-- The standard ordered exterior basis maps to the occupation basis. -/
theorem fermionExteriorToOccupation_basis (s : Finset (Fin m)) :
    fermionExteriorToOccupation ((Pi.basisFun ℂ (Fin m)).ExteriorAlgebra s) =
      EuclideanSpace.single (fun k => decide (k ∈ s)) (1 : ℂ) := by
  classical
  rw [ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    Function.comp_def, Pi.basisFun_apply, Set.powersetCard.prodEquiv_symm_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change fermionExteriorToOccupation
      ((List.ofFn fun i : Fin s.card =>
        ExteriorAlgebra.ι ℂ (Pi.single (s.orderEmbOfFin rfl i) (1 : ℂ)))).prod = _
  have hlist : (List.ofFn fun i : Fin s.card => s.orderEmbOfFin rfl i) = s.sort := by
    rw [List.ofFn_eq_map]
    exact Finset.listMap_orderEmbOfFin_finRange s rfl
  have hmap : (List.ofFn fun i : Fin s.card =>
      ExteriorAlgebra.ι ℂ (Pi.single (s.orderEmbOfFin rfl i) (1 : ℂ))) =
      (s.sort.map fun k => ExteriorAlgebra.ι ℂ (Pi.single k (1 : ℂ))) := by
    rw [← hlist, List.map_ofFn]
    rfl
  rw [hmap, fermionExteriorToOccupation_basis_word,
    fermionCreationWord_eq_single (Finset.sortedLT_sort s).pairwise]
  congr 1
  funext k
  simp

/-- Finite subsets of modes and occupation bitstrings describe the same basis. -/
def occupationFinsetEquiv : Finset (Fin m) ≃ Qm m where
  toFun s k := decide (k ∈ s)
  invFun x := Finset.univ.filter fun k => x k
  left_inv s := by ext k; simp
  right_inv x := by funext k; simp

/-- The exterior Fock space, identified with the occupation Hilbert space.
The Hilbert structure is supplied by these orthonormal occupation coordinates. -/
def fermionExteriorEquiv : ExteriorAlgebra ℂ (Fin m → ℂ) ≃ₗ[ℂ] HF m :=
  (Pi.basisFun ℂ (Fin m)).ExteriorAlgebra.equiv
    (EuclideanSpace.basisFun (Qm m) ℂ).toBasis occupationFinsetEquiv

theorem fermionExteriorEquiv_toLinearMap :
    (fermionExteriorEquiv (m := m)).toLinearMap = fermionExteriorToOccupation := by
  apply (Pi.basisFun ℂ (Fin m)).ExteriorAlgebra.ext
  intro s
  simp only [fermionExteriorEquiv, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    fermionExteriorToOccupation_basis]
  rfl

@[simp] theorem fermionExteriorEquiv_apply (x : ExteriorAlgebra ℂ (Fin m → ℂ)) :
    fermionExteriorEquiv x = fermionExteriorToOccupation x :=
  LinearMap.congr_fun fermionExteriorEquiv_toLinearMap x

/-- The complex one-particle action of a real mode rotation. -/
def fermionOneParticleRotation (R : FermionModeRotation m) :
    (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  Matrix.mulVecLin (R.val.map Complex.ofReal)

theorem fermionSecondQuantization_creationLinear (R : FermionModeRotation m)
    (v : Fin m → ℂ) (ψ : HF m) :
    fermionSecondQuantization R (fermionCreationLinear v ψ) =
      fermionCreationLinear (fermionOneParticleRotation R v)
        (fermionSecondQuantization R ψ) := by
  simp only [fermionCreationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    fermionSecondQuantization_creation, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [fermionOneParticleRotation, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Matrix.map_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_comm]

private theorem fermionSecondQuantization_exteriorCreation (R : FermionModeRotation m)
    (x : ExteriorAlgebra ℂ (Fin m → ℂ)) (ψ : HF m) :
    fermionSecondQuantization R (fermionExteriorCreation x ψ) =
      fermionExteriorCreation (ExteriorAlgebra.map (fermionOneParticleRotation R) x)
        (fermionSecondQuantization R ψ) := by
  induction x using ExteriorAlgebra.induction generalizing ψ with
  | algebraMap z => simp
  | ι v => simpa using fermionSecondQuantization_creationLinear R v ψ
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply]
    rw [hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The vacuum-normalized implementer is exactly the exterior-algebra map of
the one-particle rotation. Thus on each particle-number sector it is the
restriction of the tensor power, as in the manuscript's definition of Γ∧. -/
theorem fermionSecondQuantization_eq_exterior_map (R : FermionModeRotation m)
    (x : ExteriorAlgebra ℂ (Fin m → ℂ)) :
    fermionSecondQuantization R (fermionExteriorEquiv x) =
      fermionExteriorEquiv (ExteriorAlgebra.map (fermionOneParticleRotation R) x) := by
  simp only [fermionExteriorEquiv_apply]
  change fermionSecondQuantization R (fermionExteriorCreation x (fermionVacuum m)) =
    fermionExteriorCreation (ExteriorAlgebra.map (fermionOneParticleRotation R) x)
      (fermionVacuum m)
  rw [fermionSecondQuantization_exteriorCreation, fermionSecondQuantization_vacuum]

/-- On the k-particle sector, the implementer is the kth exterior power of
the one-particle rotation. -/
theorem fermionSecondQuantization_exteriorPower (R : FermionModeRotation m)
    {k : ℕ} (x : ⋀[ℂ]^k (Fin m → ℂ)) :
    fermionSecondQuantization R (fermionExteriorEquiv (x : ExteriorAlgebra ℂ (Fin m → ℂ))) =
      fermionExteriorEquiv
        (exteriorPower.map k (fermionOneParticleRotation R) x :
          ExteriorAlgebra ℂ (Fin m → ℂ)) := by
  rw [exteriorPower.coe_map, fermionSecondQuantization_eq_exterior_map]

/-- Decomposable wedges transform by applying the one-particle rotation to
each factor, the manuscript's restriction of the tensor power. -/
theorem fermionSecondQuantization_wedge (R : FermionModeRotation m)
    {k : ℕ} (v : Fin k → Fin m → ℂ) :
    fermionSecondQuantization R
        (fermionExteriorEquiv (ExteriorAlgebra.ιMulti ℂ k v)) =
      fermionExteriorEquiv
        (ExteriorAlgebra.ιMulti ℂ k (fermionOneParticleRotation R ∘ v)) := by
  rw [fermionSecondQuantization_eq_exterior_map, ExteriorAlgebra.map_apply_ιMulti]

end
end GaussianTesting
