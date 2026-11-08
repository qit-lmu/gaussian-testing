module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.Binomial
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

/-!
# The exact overlap and maximal eigenvalue in the Kac calculation

These are the coefficients `a_j` and `λ_j` in the proof of Theorem 4.1.
The alternating binomial-square sum is the middle coefficient of
`(1-X)^j (1+X)^j = (1-X²)^j`.
-/

namespace GaussianTesting

open Finset Polynomial

noncomputable section

/-- The common overlap `a_j` in the manuscript's integer-spin Gram matrix. -/
def spinOverlap (j : ℕ) : ℝ :=
  (∑ k ∈ range (j + 1), (-1 : ℝ) ^ k * (j.choose k : ℝ) ^ 2) / 2 ^ j

private theorem coeff_one_sub_X_pow (j k : ℕ) :
    ((1 - X : ℝ[X]) ^ j).coeff k = (-1 : ℝ) ^ k * j.choose k := by
  have h := Polynomial.comp_C_mul_X_coeff (p := (1 + X : ℝ[X]) ^ j) (r := (-1 : ℝ)) (n := k)
  simpa only [pow_comp, add_comp, one_comp, X_comp, map_neg, map_one, neg_one_mul,
    ← sub_eq_add_neg, coeff_one_add_X_pow, mul_comm] using h

/-- The alternating binomial-square identity used in Theorem 4.1. -/
theorem alternating_choose_sq_sum (j : ℕ) :
    (∑ k ∈ range (j + 1), (-1 : ℝ) ^ k * (j.choose k : ℝ) ^ 2) =
      if 2 ∣ j then (-1 : ℝ) ^ (j / 2) * j.choose (j / 2) else 0 := by
  have hpoly : (1 - X : ℝ[X]) ^ j * (1 + X) ^ j =
      Polynomial.expand ℝ 2 ((1 - X) ^ j) := by
    rw [← mul_pow]
    simp only [map_pow, map_sub, map_one, expand_X]
    congr 1
    ring
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff j) hpoly
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_expand (by norm_num)] at hcoeff
  simp only [coeff_one_sub_X_pow, coeff_one_add_X_pow] at hcoeff
  rw [← hcoeff]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hk)]
  ring

/-- Odd spin gives three orthogonal axis-fixed vectors. -/
theorem spinOverlap_odd {j : ℕ} (hj : Odd j) : spinOverlap j = 0 := by
  have hnot : ¬ 2 ∣ j := by
    rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := hj
    omega
  rw [spinOverlap, alternating_choose_sq_sum, ite_eq_right hnot, zero_div]

/-- Positive central-binomial magnitude of the even-spin overlap. -/
def centralOverlap (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) / 4 ^ k

/-- The manuscript's closed form for the overlap in even spin. -/
theorem spinOverlap_even (k : ℕ) : spinOverlap (2 * k) = (-1 : ℝ) ^ k * centralOverlap k := by
  rw [spinOverlap, alternating_choose_sq_sum]
  simp only [dvd_mul_right, ite_true, Nat.mul_div_right _ (by omega : 0 < 2)]
  rw [pow_mul]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  simp only [centralOverlap, Nat.centralBinom]
  ring

theorem centralOverlap_pos (k : ℕ) : 0 < centralOverlap k := by
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos k) (by positivity)

theorem centralOverlap_succ (k : ℕ) :
    centralOverlap (k + 1) = centralOverlap k * (2 * k + 1) / (2 * k + 2) := by
  have h : ((k : ℝ) + 1) * Nat.centralBinom (k + 1) =
      2 * (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  unfold centralOverlap
  rw [pow_succ]
  have hp : (4 : ℝ) ^ k ≠ 0 := by positivity
  have hk : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The absolute overlap strictly decreases along the even spins. -/
theorem centralOverlap_strictAnti : StrictAnti centralOverlap := by
  apply strictAnti_nat_of_succ_lt
  intro k
  rw [centralOverlap_succ]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k + 2)).mpr
  nlinarith [centralOverlap_pos k]

/-- The largest eigenvalue of the manuscript's three-by-three Gram matrix divided by three. -/
def spinKacMaximum (j : ℕ) : ℝ :=
  max ((1 + 2 * spinOverlap j) / 3) ((1 - spinOverlap j) / 3)

theorem spinKacMaximum_odd {j : ℕ} (hj : Odd j) : spinKacMaximum j = 1 / 3 := by
  simp [spinKacMaximum, spinOverlap_odd hj]

@[simp] theorem spinOverlap_two : spinOverlap 2 = -1 / 2 := by
  norm_num [spinOverlap, Finset.sum_range_succ, Nat.choose]

@[simp] theorem spinOverlap_four : spinOverlap 4 = 3 / 8 := by
  norm_num [spinOverlap, Finset.sum_range_succ, Nat.choose]

@[simp] theorem spinKacMaximum_two : spinKacMaximum 2 = 1 / 2 := by
  norm_num [spinKacMaximum]

@[simp] theorem spinKacMaximum_four : spinKacMaximum 4 = 7 / 12 := by
  norm_num [spinKacMaximum]

theorem spinKacMaximum_le_abs (j : ℕ) :
    spinKacMaximum j ≤ (1 + 2 * |spinOverlap j|) / 3 := by
  apply max_le
  · linarith [le_abs_self (spinOverlap j)]
  · linarith [neg_le_abs (spinOverlap j), abs_nonneg (spinOverlap j)]

/-- Every integer spin `j ≥ 6` has maximal eigenvalue strictly smaller than `7/12`. -/
theorem spinKacMaximum_lt_of_six_le {j : ℕ} (hj : 6 ≤ j) : spinKacMaximum j < 7 / 12 := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨k, rfl⟩ := he
    have hk : 2 < k := by omega
    have h := centralOverlap_strictAnti hk
    have hc : centralOverlap 2 = 3 / 8 := by norm_num [centralOverlap, Nat.centralBinom, Nat.choose]
    rw [hc] at h
    have ha : |spinOverlap (k + k)| = centralOverlap k := by
      rw [show k + k = 2 * k by omega, spinOverlap_even, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul, abs_of_pos (centralOverlap_pos k)]
    have hb := spinKacMaximum_le_abs (k + k)
    rw [ha] at hb
    linarith
  · rw [spinKacMaximum_odd ho]
    norm_num

/-- The maximum is positive for every integer spin. -/
theorem spinKacMaximum_pos (j : ℕ) : 0 < spinKacMaximum j := by
  have h₁ := le_max_left ((1 + 2 * spinOverlap j) / 3) ((1 - spinOverlap j) / 3)
  have h₂ := le_max_right ((1 + 2 * spinOverlap j) / 3) ((1 - spinOverlap j) / 3)
  change 0 < spinKacMaximum j
  dsimp [spinKacMaximum]
  linarith

/-- The uniform `7/12` upper bound, now obtained from the exact integer-spin maximum. -/
theorem spinKacMaximum_le {j : ℕ} (hj : 0 < j) : spinKacMaximum j ≤ 7 / 12 := by
  by_cases h : 6 ≤ j
  · exact (spinKacMaximum_lt_of_six_le h).le
  · interval_cases j <;> norm_num [spinKacMaximum, spinOverlap, Finset.sum_range_succ, Nat.choose] at *

end
end GaussianTesting
