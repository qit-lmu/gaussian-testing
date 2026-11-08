module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberPolynomial
public import GaussianTesting.Bosons.SchrodingerAdjoint

@[expose] public section

/-! # Inner products of oscillator number polynomials

The canonical commutation relations and Gaussian integration by parts give
orthogonality and factorial norms of the ordered creation powers.
-/

namespace GaussianTesting

open MvPolynomial
open scoped InnerProductSpace

noncomputable section

variable {σ : Type*}

/-- A creation word is an eigenvector of each mode's number operator. -/
theorem creationWord_number [DecidableEq σ] (j : σ) (l : List σ) :
    polynomialCreation j (polynomialAnnihilation j (creationWord l)) =
      (l.count j : ℂ) • creationWord l := by
  induction l with
  | nil => simp [polynomialAnnihilation_apply]
  | cons k l ih =>
    rw [creationWord_cons, polynomialAnnihilation_creation, map_add,
      polynomialCreation_commute j k, ih, map_smul]
    by_cases h : j = k
    · subst k
      simp only [ite_true, List.count_cons_self, Nat.cast_add, Nat.cast_one,
        add_smul, one_smul]
    · simp [h, Ne.symm h]

variable [Fintype σ]

/-- The polynomial number operator is symmetric for the actual `L²` inner product. -/
theorem inner_polynomialGaussian_number (P Q : MvPolynomial σ ℂ) (j : σ) :
    inner ℂ (polynomialGaussian (polynomialCreation j (polynomialAnnihilation j P)))
        (polynomialGaussian Q) =
      inner ℂ (polynomialGaussian P)
        (polynomialGaussian (polynomialCreation j (polynomialAnnihilation j Q))) := by
  rw [inner_polynomialGaussian_creation, inner_polynomialGaussian_annihilation]

/-- Different occupation numbers give orthogonal Gaussian wavefunctions. -/
theorem inner_creationWord_eq_zero [DecidableEq σ] (l k : List σ) (j : σ)
    (h : l.count j ≠ k.count j) :
    inner ℂ (polynomialGaussian (creationWord l)) (polynomialGaussian (creationWord k)) = 0 := by
  have he := inner_polynomialGaussian_number (creationWord l) (creationWord k) j
  rw [creationWord_number, creationWord_number, polynomialGaussian_smul,
    polynomialGaussian_smul, inner_smul_left, inner_smul_right] at he
  simp only [map_natCast] at he
  exact (mul_eq_mul_right_iff.mp he).resolve_left (by exact_mod_cast h)

/-- Adding one creation operator multiplies the squared norm by the new occupation. -/
theorem inner_creationWord_cons_self [DecidableEq σ] (j : σ) (l : List σ) :
    inner ℂ (polynomialGaussian (creationWord (j :: l)))
        (polynomialGaussian (creationWord (j :: l))) =
      ((l.count j : ℂ) + 1) *
        inner ℂ (polynomialGaussian (creationWord l)) (polynomialGaussian (creationWord l)) := by
  rw [creationWord_cons, inner_polynomialGaussian_creation,
    polynomialAnnihilation_creation]
  simp only [ite_true, creationWord_number, polynomialGaussian_add,
    polynomialGaussian_smul, inner_add_right, inner_smul_right]
  ring

private theorem count_factorial_prod_cons [DecidableEq σ] (j : σ) (l : List σ) :
    (∏ i, ((j :: l).count i).factorial : ℕ) =
      (l.count j + 1) * ∏ i, (l.count i).factorial := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have he : (∏ i ∈ Finset.univ.erase j, ((j :: l).count i).factorial) =
      ∏ i ∈ Finset.univ.erase j, (l.count i).factorial := by
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ≠ j := (Finset.mem_erase.mp hi).1
    simp [Ne.symm hn]
  rw [he, List.count_cons_self, Nat.factorial_succ]
  ring

/-- The squared norm of an unnormalized creation word is the occupation factorial
times the squared norm of the unnormalized Gaussian. -/
theorem inner_creationWord_self [DecidableEq σ] (l : List σ) :
    inner ℂ (polynomialGaussian (creationWord l)) (polynomialGaussian (creationWord l)) =
      (∏ j, ((l.count j).factorial : ℂ)) *
        inner ℂ (polynomialGaussian (1 : MvPolynomial σ ℂ))
          (polynomialGaussian (1 : MvPolynomial σ ℂ)) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [inner_creationWord_cons_self, ih]
    have h : (∏ i, (((j :: l).count i).factorial : ℂ)) =
        ((l.count j : ℂ) + 1) * ∏ i, ((l.count i).factorial : ℂ) := by
      exact_mod_cast count_factorial_prod_cons j l
    rw [h]
    ring

/-- Ordered number polynomials with different occupation vectors are orthogonal. -/
theorem inner_fockNumberPolynomialRaw_eq_zero (n k : σ → ℕ) (h : n ≠ k) :
    inner ℂ (polynomialGaussian (fockNumberPolynomialRaw n))
      (polynomialGaussian (fockNumberPolynomialRaw k)) = 0 := by
  classical
  obtain ⟨l,hl,he⟩ := exists_creationWord_eq_raw n
  obtain ⟨s,hs,hf⟩ := exists_creationWord_eq_raw k
  obtain ⟨j,hj⟩ : ∃ j, n j ≠ k j := Function.ne_iff.mp h
  rw [← he, ← hf]
  exact inner_creationWord_eq_zero l s j (by simpa only [hl,hs] using hj)

/-- Ordered creation powers have the product-factorial squared norm. -/
theorem inner_fockNumberPolynomialRaw_self (n : σ → ℕ) :
    inner ℂ (polynomialGaussian (fockNumberPolynomialRaw n))
        (polynomialGaussian (fockNumberPolynomialRaw n)) =
      (∏ j, ((n j).factorial : ℂ)) *
        inner ℂ (polynomialGaussian (1 : MvPolynomial σ ℂ))
          (polynomialGaussian (1 : MvPolynomial σ ℂ)) := by
  classical
  obtain ⟨l,hl,he⟩ := exists_creationWord_eq_raw n
  simpa only [he, hl] using inner_creationWord_self l

end
end GaussianTesting
