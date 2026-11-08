module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.Lambda
public import GaussianTesting.Fermions.MajoranaCommutant

@[expose] public section

/-!
# The two-copy Majoranas in occupation coordinates

This is the actual unitary `H_(2m) ≃ H_m ⊗ H_m` at the manuscript's
Eq. (5.4), with modes ordered by copy and then by mode. It transports the
Jordan--Wigner Majoranas to `c_j ⊗ I` and `Π ⊗ c_j`.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- Copy-major indexing for two sets of modes. -/
abbrev fermionPairCopyMode (a : Fin 2) (k : Fin m) : Fin (2 * m) :=
  finProdFinEquiv (a, k)

/-- Occupation vector in one of the two copies. -/
def pairOccupation (x : Qm m × Qm m) : Fin 2 → Qm m := ![x.1, x.2]

/-- Splitting a `2m`-mode occupation vector into two `m`-mode vectors. -/
def fermionPairOccupationEquiv (m : ℕ) : Qm (2 * m) ≃ Qm m × Qm m where
  toFun x := (fun k => x (fermionPairCopyMode 0 k), fun k => x (fermionPairCopyMode 1 k))
  invFun x i := pairOccupation x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv x := by
    funext i
    obtain ⟨⟨a, k⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp only [Equiv.symm_apply_apply]
    fin_cases a <;> rfl
  right_inv x := by
    rcases x with ⟨x, y⟩
    simp [fermionPairCopyMode, pairOccupation]

@[simp] theorem fermionPairOccupationEquiv_symm_apply
    (x : Qm m × Qm m) (a : Fin 2) (k : Fin m) :
    (fermionPairOccupationEquiv m).symm x (fermionPairCopyMode a k) = pairOccupation x a k := by
  change pairOccupation x (finProdFinEquiv.symm (finProdFinEquiv (a, k))).1
    (finProdFinEquiv.symm (finProdFinEquiv (a, k))).2 = _
  simp

/-- The unitary occupation identification `H_(2m) = H_m^⊗2`. -/
def fermionPairEquiv (m : ℕ) : HF (2 * m) ≃ₗᵢ[ℂ] H2 (Qm m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (fermionPairOccupationEquiv m)

@[simp] theorem fermionPairEquiv_apply (ψ : HF (2 * m)) (x : Qm m × Qm m) :
    fermionPairEquiv m ψ x = ψ ((fermionPairOccupationEquiv m).symm x) := rfl

@[simp] theorem fermionPairEquiv_symm_apply (ψ : H2 (Qm m)) (x : Qm (2 * m)) :
    (fermionPairEquiv m).symm ψ x = ψ (fermionPairOccupationEquiv m x) := by
  simp [fermionPairEquiv, LinearIsometryEquiv.piLpCongrLeft_symm, Equiv.piCongrLeft']

private theorem pairCopyMode_lt (a b : Fin 2) (k l : Fin m) :
    fermionPairCopyMode a k < fermionPairCopyMode b l ↔ a < b ∨ a = b ∧ k < l := by
  simp only [fermionPairCopyMode, finProdFinEquiv, Equiv.coe_fn_mk, Fin.lt_def]
  fin_cases a <;> fin_cases b <;> simp <;> omega

private theorem occupationParity_eq_prod (x : Qm m) :
    (-1 : ℂ) ^ (Finset.univ.filter fun k => x k).card =
      ∏ k, (if x k then (-1 : ℂ) else 1) := by
  rw [← Finset.prod_filter]
  simp

/-- The Jordan--Wigner prefix separates into the parity of earlier copies and
its within-copy prefix. -/
theorem jwSign_fermionPairCopyMode (x : Qm (2 * m)) (a : Fin 2) (k : Fin m) :
    jwSign x (fermionPairCopyMode a k) =
      (∏ b ∈ Finset.univ.filter (fun b : Fin 2 => b < a),
        (-1 : ℂ) ^ (Finset.univ.filter fun l : Fin m => x (fermionPairCopyMode b l)).card) *
      jwSign (fun l => x (fermionPairCopyMode a l)) k := by
  classical
  simp only [jwSign, Finset.prod_filter]
  rw [← Equiv.prod_comp finProdFinEquiv]
  simp only [Fintype.prod_prod_type, pairCopyMode_lt]
  have hp (b : Fin 2) :
      (∏ l : Fin m, if b < a ∨ b = a ∧ l < k then
        (if x (fermionPairCopyMode b l) then (-1 : ℂ) else 1) else 1) =
      (if b < a then ∏ l : Fin m, (if x (fermionPairCopyMode b l) then (-1 : ℂ) else 1)
        else 1) *
      (if b = a then ∏ l : Fin m, if l < k then
        (if x (fermionPairCopyMode b l) then (-1 : ℂ) else 1) else 1 else 1) := by
    by_cases hba : b < a
    · simp [hba, ne_of_lt hba]
    · by_cases heq : b = a <;> simp [hba, heq]
  simp_rw [hp, ← occupationParity_eq_prod]
  rw [Finset.prod_mul_distrib]
  simp

private theorem pair_split_flipBit (x : Qm (2 * m)) (a : Fin 2) (k : Fin m) :
    fermionPairOccupationEquiv m (flipBit (fermionPairCopyMode a k) x) =
      ![(flipBit k (fun l => x (fermionPairCopyMode 0 l)),
          (fun l => x (fermionPairCopyMode 1 l))),
        ((fun l => x (fermionPairCopyMode 0 l)),
          flipBit k (fun l => x (fermionPairCopyMode 1 l)))] a := by
  classical
  fin_cases a <;> ext l <;>
    simp [fermionPairOccupationEquiv, fermionPairCopyMode, flipBit, Function.update_apply]

private theorem pair_split_occupation_apply (x : Qm (2 * m)) :
    fermionPairOccupationEquiv m x =
      ((fun k => x (fermionPairCopyMode 0 k)), (fun k => x (fermionPairCopyMode 1 k))) := rfl

/-- The first set of two-copy Majoranas `c_j ⊗ I`. -/
def maj2₁ (b : Fin m × Bool) : Module.End ℂ (H2 (Qm m)) := opL (maj b)

/-- The second set of two-copy Majoranas `Π ⊗ c_j`. -/
def maj2₂ (b : Fin m × Bool) : Module.End ℂ (H2 (Qm m)) :=
  opL parityOp ∘ₗ opR (maj b)

/-- The parity-string Majorana in either copy. -/
def fermionPairMajorana (a : Fin 2) (b : Fin m × Bool) : Module.End ℂ (H2 (Qm m)) :=
  ![maj2₁ b, maj2₂ b] a

private theorem maj2_first_apply (b : Fin m × Bool) (ψ : H2 (Qm m)) (x : Qm m × Qm m) :
    maj2₁ b ψ x = jwSign x.1 b.1 * majFactor b.2 (x.1 b.1) * ψ (flipBit b.1 x.1, x.2) := rfl

private theorem maj2_second_apply (b : Fin m × Bool) (ψ : H2 (Qm m)) (x : Qm m × Qm m) :
    maj2₂ b ψ x = (-1 : ℂ) ^ (Finset.univ.filter fun k => x.1 k).card *
      (jwSign x.2 b.1 * majFactor b.2 (x.2 b.1) * ψ (x.1, flipBit b.1 x.2)) := rfl

/-- The two-copy occupation unitary transports the original Majoranas to
exactly the manuscript's two parity strings. -/
theorem fermionPairEquiv_majorana (a : Fin 2) (b : Fin m × Bool) (ψ : HF (2 * m)) :
    fermionPairEquiv m (maj (fermionPairCopyMode a b.1, b.2) ψ) =
      fermionPairMajorana a b (fermionPairEquiv m ψ) := by
  classical
  apply (fermionPairEquiv m).symm.injective
  simp only [LinearIsometryEquiv.symm_apply_apply]
  ext x
  have hinv := (fermionPairOccupationEquiv m).symm_apply_apply
    (flipBit (fermionPairCopyMode a b.1) x)
  rw [pair_split_flipBit] at hinv
  rw [maj_apply, jwSign_fermionPairCopyMode]
  fin_cases a <;> simp at hinv
  all_goals
    simp only [fermionPairEquiv_symm_apply]
    simp [fermionPairMajorana, maj2_first_apply, maj2_second_apply, pair_split_occupation_apply,
      fermionPairEquiv_apply, Finset.prod_filter, hinv]
  all_goals ring

/-- Each two-copy Majorana squares to the identity. -/
theorem fermionPairMajorana_sq (a : Fin 2) (b : Fin m × Bool) :
    fermionPairMajorana a b * fermionPairMajorana a b = 1 := by
  apply LinearMap.ext
  intro φ
  obtain ⟨ψ, rfl⟩ := (fermionPairEquiv m).surjective φ
  change fermionPairMajorana a b (fermionPairMajorana a b (fermionPairEquiv m ψ)) = _
  rw [← fermionPairEquiv_majorana, ← fermionPairEquiv_majorana]
  exact congrArg (fermionPairEquiv m) (LinearMap.congr_fun (maj_sq _) ψ)

/-- Distinct two-copy Majoranas anticommute. -/
theorem fermionPairMajorana_anticomm (a c : Fin 2) (b d : Fin m × Bool)
    (h : (a, b) ≠ (c, d)) :
    fermionPairMajorana a b * fermionPairMajorana c d +
      fermionPairMajorana c d * fermionPairMajorana a b = 0 := by
  have hidx : (fermionPairCopyMode a b.1, b.2) ≠ (fermionPairCopyMode c d.1, d.2) := by
    intro he
    have hm := finProdFinEquiv.injective (Prod.mk.inj he).1
    exact h (by cases b; cases d; simp_all [Prod.mk.injEq])
  apply LinearMap.ext
  intro φ
  obtain ⟨ψ, rfl⟩ := (fermionPairEquiv m).surjective φ
  change fermionPairMajorana a b (fermionPairMajorana c d (fermionPairEquiv m ψ)) +
    fermionPairMajorana c d (fermionPairMajorana a b (fermionPairEquiv m ψ)) = 0
  rw [← fermionPairEquiv_majorana, ← fermionPairEquiv_majorana,
    ← fermionPairEquiv_majorana, ← fermionPairEquiv_majorana, ← map_add]
  rw [show maj (fermionPairCopyMode a b.1, b.2) (maj (fermionPairCopyMode c d.1, d.2) ψ) +
      maj (fermionPairCopyMode c d.1, d.2) (maj (fermionPairCopyMode a b.1, b.2) ψ) = 0 from
    LinearMap.congr_fun (maj_anticomm hidx) ψ, map_zero]

/-- Two-copy Majoranas are Hermitian under the occupation identification. -/
theorem fermionPairMajorana_isSymmetric (a : Fin 2) (b : Fin m × Bool) :
    (fermionPairMajorana a b).IsSymmetric := by
  intro f g
  obtain ⟨v, rfl⟩ := (fermionPairEquiv m).surjective f
  obtain ⟨w, rfl⟩ := (fermionPairEquiv m).surjective g
  rw [← fermionPairEquiv_majorana, ← fermionPairEquiv_majorana]
  simpa only [LinearIsometryEquiv.inner_map_map] using
    maj_isSymmetric (fermionPairCopyMode a b.1, b.2) v w

/-- The occupation identification preserves the two-copy vacuum. -/
theorem fermionPairEquiv_vacuum :
    fermionPairEquiv m (EuclideanSpace.single (fun _ => false) 1) =
      tp2 (EuclideanSpace.single (fun _ => false) 1)
        (EuclideanSpace.single (fun _ => false) 1) := by
  classical
  ext x
  simp only [fermionPairEquiv_apply, EuclideanSpace.single, PiLp.single_apply, tp2_apply]
  have heq : (fermionPairOccupationEquiv m).symm x = (fun _ => false) ↔
      x = ((fun _ => false), (fun _ => false)) := by
    rw [Equiv.symm_apply_eq]
    rfl
  rcases x with ⟨x, y⟩
  simp only [heq, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The transported two-copy Majoranas have scalar commutant. -/
theorem exists_scalar_of_commutes_fermionPairMajorana
    (A : H2 (Qm m) →ₗ[ℂ] H2 (Qm m))
    (hA : ∀ r b ψ, A (fermionPairMajorana r b ψ) = fermionPairMajorana r b (A ψ)) :
    ∃ z : ℂ, A = z • LinearMap.id := by
  let E := fermionPairEquiv m
  let B := E.symm.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ E.toLinearEquiv.toLinearMap
  have hB : ∀ a, B ∘ₗ maj a = maj a ∘ₗ B := by
    rintro ⟨i, t⟩
    obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective i
    apply LinearMap.ext
    intro ψ
    apply E.injective
    change E (E.symm (A (E (maj (fermionPairCopyMode r k, t) ψ)))) =
      E (maj (fermionPairCopyMode r k, t) (E.symm (A (E ψ))))
    simp only [E, LinearIsometryEquiv.apply_symm_apply]
    rw [fermionPairEquiv_majorana r (k, t), fermionPairEquiv_majorana r (k, t)]
    simp only [LinearIsometryEquiv.apply_symm_apply]
    exact hA r (k, t) (E ψ)
  obtain ⟨z, hz⟩ := exists_scalar_of_commutes_maj B hB
  refine ⟨z, ?_⟩
  apply LinearMap.ext
  intro ψ
  have h := congrArg (fun C : HF (2 * m) →ₗ[ℂ] HF (2 * m) => E (C (E.symm ψ))) hz
  simpa [B] using h

end
end GaussianTesting
