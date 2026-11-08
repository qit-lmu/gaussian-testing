module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.SO3Bridge
public import GaussianTesting.Fermions.MajoranaCommutant

@[expose] public section

/-!
# Three-copy occupation coordinates

The occupation identification in the proof of Theorem 5.2 orders modes by
copy first and mode second. Under this identification the Jordan--Wigner
Majoranas on `3m` modes are exactly the manuscript's parity-string Majoranas.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- Copy-major mode indexing: `(a,k)` has index `a*m+k`. -/
abbrev fermionCopyMode (a : Fin 3) (k : Fin m) : Fin (3 * m) :=
  finProdFinEquiv (a, k)

/-- Reading the occupation vector in one of the three copies. -/
def tripleOccupation (x : Qm m × Qm m × Qm m) : Fin 3 → Qm m :=
  ![x.1, x.2.1, x.2.2]

/-- Splitting a `3m`-mode occupation vector into three `m`-mode vectors. -/
def fermionTripleOccupationEquiv (m : ℕ) : Qm (3 * m) ≃ Qm m × Qm m × Qm m where
  toFun x := (fun k => x (fermionCopyMode 0 k),
    fun k => x (fermionCopyMode 1 k), fun k => x (fermionCopyMode 2 k))
  invFun x i := tripleOccupation x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv x := by
    funext i
    obtain ⟨⟨a, k⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp only [Equiv.symm_apply_apply]
    fin_cases a <;> rfl
  right_inv x := by
    rcases x with ⟨x, y, z⟩
    simp [fermionCopyMode, tripleOccupation]

@[simp] theorem fermionTripleOccupationEquiv_symm_apply
    (x : Qm m × Qm m × Qm m) (a : Fin 3) (k : Fin m) :
    (fermionTripleOccupationEquiv m).symm x (fermionCopyMode a k) =
      tripleOccupation x a k := by
  change tripleOccupation x (finProdFinEquiv.symm (finProdFinEquiv (a, k))).1
    (finProdFinEquiv.symm (finProdFinEquiv (a, k))).2 = _
  simp

/-- The unitary occupation-coordinate identification `H_(3m) = H_m^⊗3`. -/
def fermionTripleEquiv (m : ℕ) : HF (3 * m) ≃ₗᵢ[ℂ] H3 (Qm m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (fermionTripleOccupationEquiv m)

@[simp] theorem fermionTripleEquiv_apply (ψ : HF (3 * m))
    (x : Qm m × Qm m × Qm m) :
    fermionTripleEquiv m ψ x = ψ ((fermionTripleOccupationEquiv m).symm x) := rfl

@[simp] theorem fermionTripleEquiv_symm_apply (ψ : H3 (Qm m)) (x : Qm (3 * m)) :
    (fermionTripleEquiv m).symm ψ x = ψ (fermionTripleOccupationEquiv m x) := by
  simp [fermionTripleEquiv, LinearIsometryEquiv.piLpCongrLeft_symm,
    Equiv.piCongrLeft']

private theorem copyMode_lt (a b : Fin 3) (k l : Fin m) :
    fermionCopyMode a k < fermionCopyMode b l ↔ a < b ∨ a = b ∧ k < l := by
  simp only [fermionCopyMode, finProdFinEquiv, Equiv.coe_fn_mk, Fin.lt_def]
  fin_cases a <;> fin_cases b <;> simp <;> omega

private theorem occupationParity_eq_prod (x : Qm m) :
    (-1 : ℂ) ^ (Finset.univ.filter fun k => x k).card =
      ∏ k, (if x k then (-1 : ℂ) else 1) := by
  rw [← Finset.prod_filter]
  simp

theorem jwSign_fermionCopyMode (x : Qm (3 * m)) (a : Fin 3) (k : Fin m) :
    jwSign x (fermionCopyMode a k) =
      (∏ b ∈ Finset.univ.filter (fun b : Fin 3 => b < a),
        (-1 : ℂ) ^ (Finset.univ.filter fun l : Fin m => x (fermionCopyMode b l)).card) *
      jwSign (fun l => x (fermionCopyMode a l)) k := by
  classical
  simp only [jwSign, Finset.prod_filter]
  rw [← Equiv.prod_comp finProdFinEquiv]
  simp only [Fintype.prod_prod_type, copyMode_lt]
  have hp (b : Fin 3) :
      (∏ l : Fin m, if b < a ∨ b = a ∧ l < k then
        (if x (fermionCopyMode b l) then (-1 : ℂ) else 1) else 1) =
      (if b < a then ∏ l : Fin m, (if x (fermionCopyMode b l) then (-1 : ℂ) else 1)
        else 1) *
      (if b = a then ∏ l : Fin m, if l < k then
        (if x (fermionCopyMode b l) then (-1 : ℂ) else 1) else 1 else 1) := by
    by_cases hba : b < a
    · simp [hba, ne_of_lt hba]
    · by_cases heq : b = a <;> simp [hba, heq]
  simp_rw [hp, ← occupationParity_eq_prod]
  rw [Finset.prod_mul_distrib]
  simp

private theorem split_flipBit (x : Qm (3 * m)) (a : Fin 3) (k : Fin m) :
    fermionTripleOccupationEquiv m (flipBit (fermionCopyMode a k) x) =
      ![(flipBit k (fun l => x (fermionCopyMode 0 l)),
          (fun l => x (fermionCopyMode 1 l)), (fun l => x (fermionCopyMode 2 l))),
        ((fun l => x (fermionCopyMode 0 l)),
          flipBit k (fun l => x (fermionCopyMode 1 l)), (fun l => x (fermionCopyMode 2 l))),
        ((fun l => x (fermionCopyMode 0 l)),
          (fun l => x (fermionCopyMode 1 l)), flipBit k (fun l => x (fermionCopyMode 2 l)))] a := by
  classical
  fin_cases a <;> ext l <;>
    simp [fermionTripleOccupationEquiv, fermionCopyMode, flipBit,
      Function.update_apply]

private theorem split_occupation_apply (x : Qm (3 * m)) :
    fermionTripleOccupationEquiv m x =
      ((fun k => x (fermionCopyMode 0 k)), (fun k => x (fermionCopyMode 1 k)),
        (fun k => x (fermionCopyMode 2 k))) := rfl

private theorem maj3_first_apply (b : Fin m × Bool) (ψ : H3 (Qm m))
    (x : Qm m × Qm m × Qm m) :
    maj3₁ b ψ x = jwSign x.1 b.1 * majFactor b.2 (x.1 b.1) *
      ψ (flipBit b.1 x.1, x.2.1, x.2.2) := rfl

private theorem maj3_second_apply (b : Fin m × Bool) (ψ : H3 (Qm m))
    (x : Qm m × Qm m × Qm m) :
    maj3₂ b ψ x = (-1 : ℂ) ^ (Finset.univ.filter fun k => x.1 k).card *
      (jwSign x.2.1 b.1 * majFactor b.2 (x.2.1 b.1) *
        ψ (x.1, flipBit b.1 x.2.1, x.2.2)) := rfl

private theorem maj3_third_apply (b : Fin m × Bool) (ψ : H3 (Qm m))
    (x : Qm m × Qm m × Qm m) :
    maj3₃ b ψ x = (-1 : ℂ) ^ (Finset.univ.filter fun k => x.1 k).card *
      ((-1 : ℂ) ^ (Finset.univ.filter fun k => x.2.1 k).card *
        (jwSign x.2.2 b.1 * majFactor b.2 (x.2.2 b.1) *
          ψ (x.1, x.2.1, flipBit b.1 x.2.2))) := rfl

/-- Under occupation coordinates the three sets of Majoranas acquire exactly
 the parity strings displayed in the proof of Theorem 5.2. -/
theorem fermionTripleEquiv_majorana (a : Fin 3) (b : Fin m × Bool)
    (ψ : HF (3 * m)) :
    fermionTripleEquiv m (maj (fermionCopyMode a b.1, b.2) ψ) =
      ![maj3₁ b, maj3₂ b, maj3₃ b] a (fermionTripleEquiv m ψ) := by
  classical
  apply (fermionTripleEquiv m).symm.injective
  simp only [LinearIsometryEquiv.symm_apply_apply]
  ext x
  have hinv := (fermionTripleOccupationEquiv m).symm_apply_apply
    (flipBit (fermionCopyMode a b.1) x)
  rw [split_flipBit] at hinv
  rw [maj_apply, jwSign_fermionCopyMode]
  fin_cases a <;> simp at hinv
  all_goals
    simp only [fermionTripleEquiv_symm_apply]
    simp [maj3_first_apply, maj3_second_apply, maj3_third_apply, split_occupation_apply,
      fermionTripleEquiv_apply, Finset.prod_filter, Fin.prod_univ_succ, hinv]
  all_goals ring

/-- The occupation identification preserves the vacuum. -/
theorem fermionTripleEquiv_vacuum :
    fermionTripleEquiv m (EuclideanSpace.single (fun _ => false) 1) =
      tp3 (EuclideanSpace.single (fun _ => false) 1)
        (EuclideanSpace.single (fun _ => false) 1)
        (EuclideanSpace.single (fun _ => false) 1) := by
  classical
  ext x
  simp only [fermionTripleEquiv_apply, EuclideanSpace.single, PiLp.single_apply,
    tp3_apply]
  have heq : (fermionTripleOccupationEquiv m).symm x = (fun _ => false) ↔
      x = ((fun _ => false), (fun _ => false), (fun _ => false)) := by
    rw [Equiv.symm_apply_eq]
    rfl
  rcases x with ⟨x, y, z⟩
  simp only [heq, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The transported three-copy Majoranas have scalar commutant. -/
theorem exists_scalar_of_commutes_fermionCubeMajorana
    (A : H3 (Qm m) →ₗ[ℂ] H3 (Qm m))
    (hA : ∀ r b ψ, A (fermionCubeMajorana r b ψ) = fermionCubeMajorana r b (A ψ)) :
    ∃ z : ℂ, A = z • LinearMap.id := by
  let E := fermionTripleEquiv m
  let B := E.symm.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ E.toLinearEquiv.toLinearMap
  have hB : ∀ a, B ∘ₗ maj a = maj a ∘ₗ B := by
    rintro ⟨i, t⟩
    obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective i
    apply LinearMap.ext
    intro ψ
    apply E.injective
    change E (E.symm (A (E (maj (fermionCopyMode r k, t) ψ)))) =
      E (maj (fermionCopyMode r k, t) (E.symm (A (E ψ))))
    simp only [E, LinearIsometryEquiv.apply_symm_apply]
    rw [fermionTripleEquiv_majorana r (k, t), fermionTripleEquiv_majorana r (k, t)]
    simp only [LinearIsometryEquiv.apply_symm_apply]
    exact hA r (k, t) (E ψ)
  obtain ⟨z, hz⟩ := exists_scalar_of_commutes_maj B hB
  refine ⟨z, ?_⟩
  apply LinearMap.ext
  intro ψ
  have h := congrArg (fun C : HF (3 * m) →ₗ[ℂ] HF (3 * m) => E (C (E.symm ψ))) hz
  simpa [B] using h

end
end GaussianTesting
