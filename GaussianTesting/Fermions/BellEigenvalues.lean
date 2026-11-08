module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.BellBasis
public import GaussianTesting.Fermions.Lambda

@[expose] public section

/-!
# The classical fermionic Bell readout in Figure 1(a)

The two bit strings label the phase and parity of the local Bell outcomes.
Every `c_j ⊗ c_j` is diagonal in this basis. Its eigenvalue includes the
Jordan–Wigner prefix parity, and the test accepts when their integer sum is zero.
-/

namespace GaussianTesting

open Finset

noncomputable section

/-- The sign encoded by one classical Bell bit. -/
def fermionicBellSign (b : Bool) : ℤ := if b then -1 else 1

private theorem bellLocalAmplitude_flip (a b x y : Bool) :
    bellLocalAmplitude a b (!x) (!y) =
      (fermionicBellSign a : ℂ) * bellLocalAmplitude a b x y := by
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [bellLocalAmplitude, fermionicBellSign]

private theorem bellLocalAmplitude_support {a b x y : Bool}
    (h : bellLocalAmplitude a b x y ≠ 0) : y = Bool.xor x b := by
  by_contra hn
  exact h (by simp [bellLocalAmplitude, hn])

private theorem fermionicBellVector_flip {m : ℕ} (z : Qm m × Qm m)
    (x y : Qm m) (k : Fin m) :
    fermionicBellVector m z (flipBit k x, flipBit k y) =
      (fermionicBellSign (z.1 k) : ℂ) * fermionicBellVector m z (x, y) := by
  classical
  simp only [fermionicBellVector_apply]
  rw [← mul_prod_erase univ _ (mem_univ k), ← mul_prod_erase univ _ (mem_univ k)]
  simp only [flipBit, Function.update_self, bellLocalAmplitude_flip]
  have he : (∏ j ∈ univ.erase k,
      bellLocalAmplitude (z.1 j) (z.2 j) (Function.update x k (!x k) j)
        (Function.update y k (!y k) j)) =
      ∏ j ∈ univ.erase k, bellLocalAmplitude (z.1 j) (z.2 j) (x j) (y j) := by
    apply prod_congr rfl
    intro j hj
    simp only [Function.update_of_ne (mem_erase.mp hj).1]
  rw [he]
  ring

private theorem fermionicBellVector_support {m : ℕ} (z : Qm m × Qm m)
    (x y : Qm m) (h : fermionicBellVector m z (x, y) ≠ 0) :
    ∀ k, y k = Bool.xor (x k) (z.2 k) := by
  intro k
  apply bellLocalAmplitude_support
  change (∏ k, bellLocalAmplitude (z.1 k) (z.2 k) (x k) (y k)) ≠ 0 at h
  exact (Finset.prod_ne_zero_iff.mp h) k (mem_univ k)

private theorem jwSign_pair {m : ℕ} (b x y : Qm m)
    (h : ∀ j, y j = Bool.xor (x j) (b j)) (k : Fin m) :
    jwSign x k * jwSign y k = jwSign b k := by
  simp only [jwSign, ← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  rw [h j]
  cases x j <;> cases b j <;> norm_num

private theorem majFactor_pair (b x y : Bool) (h : y = Bool.xor x b) (c : Bool) :
    majFactor c x * majFactor c y =
      (if c then -(fermionicBellSign b : ℂ) else 1) := by
  subst y
  cases b <;> cases x <;> cases c <;> simp [majFactor, fermionicBellSign]

/-- The integer eigenvalue of `c_{k,c} ⊗ c_{k,c}` in a product Bell outcome. -/
def fermionicBellMajoranaEigenvalue {m : ℕ} (z : Qm m × Qm m)
    (a : Fin m × Bool) : ℤ :=
  (∏ l ∈ univ.filter (fun l => l < a.1), fermionicBellSign (z.2 l)) *
    fermionicBellSign (z.1 a.1) *
    (if a.2 then -fermionicBellSign (z.2 a.1) else 1)

private theorem cast_fermionicBellMajoranaEigenvalue {m : ℕ}
    (z : Qm m × Qm m) (a : Fin m × Bool) :
    (fermionicBellMajoranaEigenvalue z a : ℂ) =
      jwSign z.2 a.1 * (fermionicBellSign (z.1 a.1) : ℂ) *
        (if a.2 then -(fermionicBellSign (z.2 a.1) : ℂ) else 1) := by
  simp [fermionicBellMajoranaEigenvalue, jwSign, fermionicBellSign]

/-- The Majorana pair observables have the stated eigenvalues in the Bell basis. -/
theorem majoranaPair_fermionicBellVector {m : ℕ} (z : Qm m × Qm m)
    (a : Fin m × Bool) :
    opL (maj a) (opR (maj a) (fermionicBellVector m z)) =
      (fermionicBellMajoranaEigenvalue z a : ℂ) • fermionicBellVector m z := by
  ext ⟨x, y⟩
  change jwSign x a.1 * majFactor a.2 (x a.1) *
      (jwSign y a.1 * majFactor a.2 (y a.1) *
        fermionicBellVector m z (flipBit a.1 x, flipBit a.1 y)) =
    (fermionicBellMajoranaEigenvalue z a : ℂ) * fermionicBellVector m z (x, y)
  rw [fermionicBellVector_flip]
  by_cases hz : fermionicBellVector m z (x, y) = 0
  · simp only [hz, mul_zero]
  have hs := fermionicBellVector_support z x y hz
  have hj := jwSign_pair z.2 x y hs a.1
  have hm := majFactor_pair (z.2 a.1) (x a.1) (y a.1) (hs a.1) a.2
  rw [cast_fermionicBellMajoranaEigenvalue]
  calc
    _ = (jwSign x a.1 * jwSign y a.1) *
        (majFactor a.2 (x a.1) * majFactor a.2 (y a.1)) *
        (fermionicBellSign (z.1 a.1) : ℂ) * fermionicBellVector m z (x, y) := by ring
    _ = _ := by rw [hj, hm]; ring

/-- The classical integer readout of `Λ`. The prefix parity is required by
the Jordan–Wigner strings; a mode contributes zero for equal-bit Bell parity. -/
def fermionicBellEigenvalue (m : ℕ) (z : Qm m × Qm m) : ℤ :=
  ∑ k, (∏ l ∈ univ.filter (fun l => l < k), fermionicBellSign (z.2 l)) *
    fermionicBellSign (z.1 k) * (1 - fermionicBellSign (z.2 k))

/-- Accept exactly the classical Bell outcomes compatible with `Λ = 0`. -/
def fermionicBellAccepts (m : ℕ) (z : Qm m × Qm m) : Prop :=
  fermionicBellEigenvalue m z = 0

private theorem fermionicBellEigenvalue_eq_sum (m : ℕ) (z : Qm m × Qm m) :
    fermionicBellEigenvalue m z = ∑ a : Fin m × Bool, fermionicBellMajoranaEigenvalue z a := by
  simp only [fermionicBellEigenvalue, Fintype.sum_prod_type, Fintype.sum_bool,
    fermionicBellMajoranaEigenvalue, Bool.false_eq_true, ↓reduceIte]
  apply sum_congr rfl
  intro k _
  ring

/-- Product Bell vectors diagonalize the manuscript's full operator `Λ`. -/
theorem lambdaF_fermionicBellVector {m : ℕ} (z : Qm m × Qm m) :
    lambdaF m (fermionicBellVector m z) =
      (fermionicBellEigenvalue m z : ℂ) • fermionicBellVector m z := by
  simp only [lambdaF, LinearMap.sum_apply, LinearMap.comp_apply,
    majoranaPair_fermionicBellVector, ← Finset.sum_smul,
    fermionicBellEigenvalue_eq_sum, Int.cast_sum]

/-- The eigenvalue formula for the orthonormal Bell basis used by the circuit. -/
theorem lambdaF_fermionicBellBasis {m : ℕ} (z : Qm m × Qm m) :
    lambdaF m (fermionicBellBasis m z) =
      (fermionicBellEigenvalue m z : ℂ) • fermionicBellBasis m z := by
  simpa only [fermionicBellBasis_apply] using lambdaF_fermionicBellVector z

end
end GaussianTesting
