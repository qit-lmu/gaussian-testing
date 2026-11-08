/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GaussianTesting.ThreeVectorGram

import Mathlib.Tactic

/-!
# The occupation-sector eigenvalues in Lemma 6.6

For `k` particles in the copy-index plane perpendicular to `(1,1,1)`, the
three distinguished unit vectors have Gram overlap `(-1/2)^k`. The two
eigenvalues below are the Gram eigenvalues divided by three. Zero Gram
eigenvalues do not contribute to the spectrum on the span of these vectors.
-/

@[expose] public section

namespace GaussianTesting

noncomputable section

/-- The eigenvalue on the constant coefficient vector in the degree-`k`
three-vector Gram calculation, divided by three. -/
def coherentSectorConstantEigenvalue (k : ℕ) : ℝ :=
  (1 + 2 * (-(1 / 2) : ℝ) ^ k) / 3

/-- The multiplicity-two eigenvalue on sum-zero coefficient vectors,
divided by three. -/
def coherentSectorSumZeroEigenvalue (k : ℕ) : ℝ :=
  (1 - (-(1 / 2) : ℝ) ^ k) / 3

/-- The largest eigenvalue on the span of the three degree-`k` vectors. -/
def coherentSectorMaxEigenvalue (k : ℕ) : ℝ :=
  max (coherentSectorConstantEigenvalue k) (coherentSectorSumZeroEigenvalue k)

/-- The exact Gram spectrum in the occupation sector used in Lemma 6.6. -/
theorem coherentSectorGram_spectrum (k : ℕ) :
    spectrum ℂ (threeVectorGram ((-(1 / 2) : ℝ) ^ k)) =
      {((3 * coherentSectorConstantEigenvalue k : ℝ) : ℂ),
       ((3 * coherentSectorSumZeroEigenvalue k : ℝ) : ℂ)} := by
  rw [threeVectorGram_spectrum]
  have hc : 3 * coherentSectorConstantEigenvalue k = 1 + 2 * (-(1 / 2) : ℝ) ^ k := by
    dsimp [coherentSectorConstantEigenvalue]
    ring
  have hz : 3 * coherentSectorSumZeroEigenvalue k = 1 - (-(1 / 2) : ℝ) ^ k := by
    dsimp [coherentSectorSumZeroEigenvalue]
    ring
  rw [hc, hz]

/-- At `k=0`, the only nonzero eigenvalue is one. -/
theorem coherentSectorEigenvalues_zero :
    coherentSectorConstantEigenvalue 0 = 1 ∧ coherentSectorSumZeroEigenvalue 0 = 0 := by
  norm_num [coherentSectorConstantEigenvalue, coherentSectorSumZeroEigenvalue]

/-- At `k=1`, the only nonzero eigenvalue is one half. -/
theorem coherentSectorEigenvalues_one :
    coherentSectorConstantEigenvalue 1 = 0 ∧ coherentSectorSumZeroEigenvalue 1 = 1 / 2 := by
  norm_num [coherentSectorConstantEigenvalue, coherentSectorSumZeroEigenvalue]

/-- At `k=2`, the eigenvalues are one half and one quarter. -/
theorem coherentSectorEigenvalues_two :
    coherentSectorConstantEigenvalue 2 = 1 / 2 ∧ coherentSectorSumZeroEigenvalue 2 = 1 / 4 := by
  norm_num [coherentSectorConstantEigenvalue, coherentSectorSumZeroEigenvalue]

theorem coherentSectorMaxEigenvalue_zero : coherentSectorMaxEigenvalue 0 = 1 := by
  norm_num [coherentSectorMaxEigenvalue, coherentSectorEigenvalues_zero.1,
    coherentSectorEigenvalues_zero.2]

theorem coherentSectorMaxEigenvalue_one : coherentSectorMaxEigenvalue 1 = 1 / 2 := by
  norm_num [coherentSectorMaxEigenvalue, coherentSectorEigenvalues_one.1,
    coherentSectorEigenvalues_one.2]

theorem coherentSectorMaxEigenvalue_two : coherentSectorMaxEigenvalue 2 = 1 / 2 := by
  norm_num [coherentSectorMaxEigenvalue, coherentSectorEigenvalues_two.1,
    coherentSectorEigenvalues_two.2]

/-- Every higher sector has largest eigenvalue strictly below one half. -/
theorem coherentSectorMaxEigenvalue_lt_half {k : ℕ} (hk : 3 ≤ k) :
    coherentSectorMaxEigenvalue k < 1 / 2 := by
  have habs : |(-(1 / 2) : ℝ) ^ k| ≤ 1 / 8 := by
    rw [abs_pow]
    norm_num
    have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hk
    norm_num at h
    exact h
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  rw [coherentSectorMaxEigenvalue, max_lt_iff]
  constructor <;> dsimp [coherentSectorConstantEigenvalue, coherentSectorSumZeroEigenvalue] <;>
    linarith

theorem coherentSectorMaxEigenvalue_le_half {k : ℕ} (hk : 0 < k) :
    coherentSectorMaxEigenvalue k ≤ 1 / 2 := by
  rcases k with _ | _ | _ | k
  · omega
  · exact coherentSectorMaxEigenvalue_one.le
  · exact coherentSectorMaxEigenvalue_two.le
  · exact (coherentSectorMaxEigenvalue_lt_half (by omega)).le

end

end GaussianTesting
