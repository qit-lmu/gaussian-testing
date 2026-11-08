module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CreationAnnihilation
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Vacuum and creation words in the occupation representation

These elementary Fock-space facts specify the second-quantized action:
the common annihilation kernel is the vacuum line, and ordered creation
words give the occupation basis.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- The fermionic vacuum occupation vector. -/
def fermionVacuum (m : ℕ) : HF m := EuclideanSpace.single (fun _ => false) 1

@[simp] theorem norm_fermionVacuum (m : ℕ) : ‖fermionVacuum m‖ = 1 := by
  simp [fermionVacuum, EuclideanSpace.single, PiLp.norm_single]

@[simp] theorem fermionAnnihilation_vacuum (k : Fin m) :
    fermionAnnihilation k (fermionVacuum m) = 0 := by
  ext x
  by_cases hx : x k = true
  · simp [fermionAnnihilation_apply, hx]
  · have hx' : x k = false := Bool.eq_false_of_not_eq_true hx
    have hne : flipBit k x ≠ (fun _ => false) := by
      intro h
      have := congrFun h k
      simp [flipBit, hx'] at this
    simp [fermionAnnihilation_apply, fermionVacuum, EuclideanSpace.single, hx', hne]

/-- A vector killed by every annihilation operator is a scalar vacuum. -/
theorem eq_smul_fermionVacuum_of_annihilation_eq_zero {ψ : HF m}
    (hψ : ∀ k, fermionAnnihilation k ψ = 0) :
    ψ = ψ (fun _ => false) • fermionVacuum m := by
  classical
  ext x
  by_cases hx : x = (fun _ => false)
  · subst x
    simp [fermionVacuum]
  · obtain ⟨k, hk⟩ : ∃ k, x k = true := by
      by_contra! h
      exact hx (funext fun k => Bool.eq_false_of_not_eq_true (h k))
    have hn : fermionNumber k ψ = 0 := by
      simp [fermionNumber, hψ]
    have hz := congrArg (fun f : HF m => f x) hn
    simp only [fermionNumber_apply, hk, ↓reduceIte, PiLp.zero_apply] at hz
    simp [fermionVacuum, EuclideanSpace.single, hx, hz]

private theorem jwSign_flip_same (x : Qm m) (k : Fin m) :
    jwSign (flipBit k x) k = jwSign x k := by
  unfold jwSign
  apply Finset.prod_congr rfl
  intro l hl
  have hne : l ≠ k := ne_of_lt (Finset.mem_filter.mp hl).2
  simp [flipBit, Function.update_of_ne hne]

/-- Creation adds an unoccupied mode, with the Jordan--Wigner ordering sign. -/
theorem fermionCreation_single (k : Fin m) (x : Qm m) :
    fermionCreation k (EuclideanSpace.single x (1 : ℂ)) =
      if x k then 0 else jwSign x k • EuclideanSpace.single (flipBit k x) 1 := by
  ext y
  by_cases hy : y = flipBit k x
  · subst y
    have hf : flipBit k x k = !x k := by simp [flipBit]
    simp only [fermionCreation_apply, hf, flipBit_flipBit, jwSign_flip_same]
    cases x k <;> simp
  · have hflip : flipBit k y ≠ x := by
      intro h
      have h' := congrArg (flipBit k) h
      simp only [flipBit_flipBit] at h'
      exact hy h'
    cases hx : x k <;>
      simp [fermionCreation_apply, EuclideanSpace.single, hy, hflip]

/-- Apply an ordered list of creation operators to the vacuum. -/
def fermionCreationWord (l : List (Fin m)) : HF m :=
  l.foldr (fun k ψ => fermionCreation k ψ) (fermionVacuum m)

/-- Increasing creation words are precisely the occupation basis, with no
additional sign in this order. -/
theorem fermionCreationWord_eq_single {l : List (Fin m)} (hl : l.Pairwise (· < ·)) :
    fermionCreationWord l =
      EuclideanSpace.single (fun k => decide (k ∈ l)) (1 : ℂ) := by
  classical
  induction l with
  | nil => simp [fermionCreationWord, fermionVacuum]
  | cons k l ih =>
    obtain ⟨hk, hl⟩ := List.pairwise_cons.mp hl
    have hnot : k ∉ l := fun h => lt_irrefl k (hk k h)
    have hsign : jwSign (fun j => decide (j ∈ l)) k = 1 := by
      unfold jwSign
      apply Finset.prod_eq_one
      intro j hj
      have hjk : j < k := (Finset.mem_filter.mp hj).2
      have hjnot : j ∉ l := fun h => (not_lt_of_gt hjk) (hk j h)
      simp [hjnot]
    have hflip : flipBit k (fun j => decide (j ∈ l)) =
        (fun j => decide (j ∈ k :: l)) := by
      funext j
      by_cases hj : j = k
      · subst j; simp [flipBit, hnot]
      · simp [flipBit, hj]
    change fermionCreation k (fermionCreationWord l) = _
    rw [ih hl, fermionCreation_single]
    simp only [hnot, decide_false, Bool.false_eq_true, ↓reduceIte, hsign, one_smul, hflip]

/-- The ordered occupied modes that create a given occupation vector. -/
def occupiedModes (x : Qm m) : List (Fin m) :=
  (Finset.univ.filter fun k => x k).sort (· ≤ ·)

theorem occupiedModes_pairwise (x : Qm m) : (occupiedModes x).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

/-- Every occupation basis vector is an explicit ordered creation word. -/
theorem fermionCreationWord_occupiedModes (x : Qm m) :
    fermionCreationWord (occupiedModes x) = EuclideanSpace.single x (1 : ℂ) := by
  rw [fermionCreationWord_eq_single (occupiedModes_pairwise x)]
  congr 1
  funext k
  simp [occupiedModes]

end
end GaussianTesting
