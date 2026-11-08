module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerNumberBasis

@[expose] public section

/-! # Creation and annihilation on the normalized number basis -/

namespace GaussianTesting

noncomputable section

variable {σ : Type*} [DecidableEq σ]

/-- Annihilation removes one occurrence of the selected mode in a creation word. -/
theorem polynomialAnnihilation_creationWord (j : σ) (l : List σ) :
    polynomialAnnihilation j (creationWord l) =
      (l.count j : ℂ) • creationWord (l.erase j) := by
  induction l with
  | nil => simp [polynomialAnnihilation_apply]
  | cons k l ih =>
    rw [creationWord_cons, polynomialAnnihilation_creation]
    by_cases h : j = k
    · subst k
      simp only [ite_true, creationWord_number, List.count_cons_self,
        List.erase_cons_head, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    · simp only [h, ite_false, add_zero, ih, map_smul]
      simp [Ne.symm h]

variable [Fintype σ]

/-- Creation increments one occupation in the unnormalized ordered powers. -/
theorem polynomialCreation_fockNumberPolynomialRaw (j : σ) (n : σ → ℕ) :
    polynomialCreation j (fockNumberPolynomialRaw n) =
      fockNumberPolynomialRaw (Function.update n j (n j + 1)) := by
  obtain ⟨l,hl,he⟩ := exists_creationWord_eq_raw n
  rw [← he, ← creationWord_cons, creationWord_eq_fockNumberPolynomialRaw]
  congr 1
  funext k
  by_cases h : k = j
  · subst k; simp [hl]
  · simp [h, Ne.symm h, hl]

/-- Annihilation has the occupation coefficient on unnormalized powers. -/
theorem polynomialAnnihilation_fockNumberPolynomialRaw (j : σ) (n : σ → ℕ) :
    polynomialAnnihilation j (fockNumberPolynomialRaw n) =
      (n j : ℂ) • fockNumberPolynomialRaw (Function.update n j (n j - 1)) := by
  obtain ⟨l,hl,he⟩ := exists_creationWord_eq_raw n
  rw [← he, polynomialAnnihilation_creationWord, creationWord_eq_fockNumberPolynomialRaw, hl]
  congr 2
  funext k
  by_cases h : k = j
  · subst k; simp [hl]
  · simp [h, hl]

/-- The real normalization factor for the manuscript's ordered creation powers. -/
def numberNormalization (n : σ → ℕ) : ℝ :=
  Real.pi ^ (-(Fintype.card σ : ℝ) / 4) /
    Real.sqrt (∏ j, ((n j).factorial : ℝ))

/-- The polynomial factor of a normalized number vector. -/
def schrodingerNumberPolynomial (n : σ → ℕ) : MvPolynomial σ ℂ :=
  (numberNormalization n : ℂ) • fockNumberPolynomialRaw n

omit [DecidableEq σ] in
theorem polynomialGaussian_schrodingerNumberPolynomial (n : σ → ℕ) :
    polynomialGaussian (schrodingerNumberPolynomial n) = schrodingerNumberVector n :=
  polynomialGaussian_smul _ _

private theorem factorial_product_update (n : σ → ℕ) (j : σ) :
    (∏ k, ((Function.update n j (n j + 1) k).factorial : ℝ)) =
      (n j + 1) * ∏ k, ((n k).factorial : ℝ) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have he : (∏ k ∈ Finset.univ.erase j, ((Function.update n j (n j + 1) k).factorial : ℝ)) =
      ∏ k ∈ Finset.univ.erase j, ((n k).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he, Function.update_self, Nat.factorial_succ]
  push_cast
  ring

theorem numberNormalization_increment (n : σ → ℕ) (j : σ) :
    numberNormalization n = Real.sqrt (n j + 1) *
      numberNormalization (Function.update n j (n j + 1)) := by
  have hp : (0 : ℝ) < ∏ k, ((n k).factorial : ℝ) :=
    Finset.prod_pos fun k _ => Nat.cast_pos.mpr (Nat.factorial_pos (n k))
  have hn : (0 : ℝ) < (n j : ℝ) + 1 := by positivity
  simp only [numberNormalization, factorial_product_update, Real.sqrt_mul hn.le]
  field_simp

/-- The usual square-root coefficient of creation on normalized number vectors. -/
theorem polynomialCreation_schrodingerNumberPolynomial (j : σ) (n : σ → ℕ) :
    polynomialCreation j (schrodingerNumberPolynomial n) =
      (Real.sqrt (n j + 1) : ℂ) •
        schrodingerNumberPolynomial (Function.update n j (n j + 1)) := by
  simp only [schrodingerNumberPolynomial, map_smul,
    polynomialCreation_fockNumberPolynomialRaw, smul_smul]
  congr 1
  exact_mod_cast numberNormalization_increment n j

/-- The usual square-root coefficient of annihilation, including occupation zero. -/
theorem polynomialAnnihilation_schrodingerNumberPolynomial (j : σ) (n : σ → ℕ) :
    polynomialAnnihilation j (schrodingerNumberPolynomial n) =
      (Real.sqrt (n j) : ℂ) •
        schrodingerNumberPolynomial (Function.update n j (n j - 1)) := by
  simp only [schrodingerNumberPolynomial, map_smul,
    polynomialAnnihilation_fockNumberPolynomialRaw, smul_smul]
  by_cases h : n j = 0
  · simp [h]
  have hn : n j - 1 + 1 = n j := by omega
  have h' := numberNormalization_increment (Function.update n j (n j - 1)) j
  simp only [Function.update_self, hn, Function.update_idem, Function.update_eq_self] at h'
  have hnr : ((n j - 1 : ℕ) : ℝ) + 1 = n j := by exact_mod_cast hn
  rw [hnr] at h'
  have he : numberNormalization n * (n j : ℝ) =
      Real.sqrt (n j) * numberNormalization (Function.update n j (n j - 1)) := by
    rw [h', ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _), mul_comm]
  congr 1
  exact_mod_cast he

end
end GaussianTesting
