module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Repeating a test on fresh copies

The product law describes independent binary measurements on disjoint fresh
copy blocks. The protocol accepts precisely when all rounds accept. The
exponential estimate and integer round count are the repetition argument in
Corollary 6.8 (and Corollary 5.3).
-/

namespace GaussianTesting

open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal

noncomputable section

/-- Independent measurement outcomes for `n` fresh copy blocks. -/
def repeatedTestLaw (p : unitInterval) (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false p)

instance repeatedTestLaw_isProbability (p : unitInterval) (n : ℕ) :
    IsProbabilityMeasure (repeatedTestLaw p n) := by
  unfold repeatedTestLaw
  infer_instance

/-- The protocol accepts exactly when every measurement round accepts. -/
def repeatedTestAccepts (n : ℕ) : Set (Fin n → Bool) := {fun _ => true}

/-- Independence gives the exact acceptance probability, including zero rounds. -/
theorem repeatedTest_acceptance (p : unitInterval) (n : ℕ) :
    (repeatedTestLaw p n).real (repeatedTestAccepts n) = (p : ℝ) ^ n := by
  simp only [repeatedTestLaw, repeatedTestAccepts, measureReal_def, Measure.pi_singleton]
  have h : bernoulliMeasure true false p {true} = (unitInterval.toNNReal p : ℝ≥0∞) :=
    bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton true)
      (Set.mem_singleton true) (by simp)
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow, ENNReal.coe_toReal]
  rfl

/-- Exact perfect completeness of the repeated protocol. -/
theorem repeatedTest_perfect_completeness (n : ℕ) :
    (repeatedTestLaw 1 n).real (repeatedTestAccepts n) = 1 := by
  simp [repeatedTest_acceptance]

/-- Rejecting means that at least one round rejects. -/
theorem repeatedTest_rejection (p : unitInterval) (n : ℕ) :
    (repeatedTestLaw p n).real (repeatedTestAccepts n)ᶜ = 1 - (p : ℝ) ^ n := by
  have hm : MeasurableSet (repeatedTestAccepts n) := measurableSet_singleton _
  rw [measureReal_compl hm, probReal_univ,
    repeatedTest_acceptance]

/-- Exponential decay for a test whose rejection probability is at least `ε²/C`. -/
theorem repeatedTest_soundness {p : unitInterval} {C ε δ : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hδ : 0 < δ)
    (hp : (p : ℝ) ≤ 1 - ε ^ 2 / C) {n : ℕ}
    (hn : C / ε ^ 2 * Real.log (1 / δ) ≤ n) :
    (repeatedTestLaw p n).real (repeatedTestAccepts n) ≤ δ := by
  rw [repeatedTest_acceptance]
  have hp0 : 0 ≤ (p : ℝ) := p.property.1
  have hb : 0 ≤ 1 - ε ^ 2 / C := hp0.trans hp
  have heps : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlog : -(n : ℝ) * (ε ^ 2 / C) ≤ Real.log δ := by
    have hn' : C / ε ^ 2 * (-Real.log δ) ≤ (n : ℝ) := by
      simpa only [one_div, Real.log_inv] using hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt (div_pos heps hC))
    have he : (C / ε ^ 2 * (-Real.log δ)) * (ε ^ 2 / C) = -Real.log δ := by
      field_simp
    rw [he] at hm
    linarith
  calc
    (p : ℝ) ^ n ≤ (1 - ε ^ 2 / C) ^ n := pow_le_pow_left₀ hp0 hp n
    _ ≤ (Real.exp (-(ε ^ 2 / C))) ^ n :=
      pow_le_pow_left₀ hb (Real.one_sub_le_exp_neg _) n
    _ = Real.exp (-(n : ℝ) * (ε ^ 2 / C)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hlog
    _ = δ := Real.exp_log hδ

/-- The integer number of rounds used for a fidelity constant `C`. -/
def testingRounds (C ε δ : ℝ) : ℕ := ⌈C / ε ^ 2 * Real.log (1 / δ)⌉₊

theorem testingRounds_sufficient (C ε δ : ℝ) :
    C / ε ^ 2 * Real.log (1 / δ) ≤ (testingRounds C ε δ : ℝ) := Nat.le_ceil _

/-- The ceiling makes the total copy bound explicit for all error parameters. -/
theorem testingCopies_le (k : ℕ) {C ε δ : ℝ} (hC : 0 ≤ C)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    (k * testingRounds C ε δ : ℕ) ≤
      (k : ℝ) * (C / ε ^ 2 * Real.log (1 / δ) + 1) := by
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg ((one_le_div hδ.1).mpr hδ.2)
  have ha : 0 ≤ C / ε ^ 2 * Real.log (1 / δ) :=
    mul_nonneg (div_nonneg hC (sq_nonneg ε)) hlog
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one ha).le (Nat.cast_nonneg k)

/-- An explicit constant for the claimed asymptotic copy rate. For error
probability at most `e⁻¹`, the ceiling costs at most a factor of two. -/
theorem testingCopies_le_rate (k : ℕ) {C ε δ : ℝ} (hC : 1 ≤ C)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (Real.exp (-1))) :
    ((k * testingRounds C ε δ : ℕ) : ℝ) ≤
      2 * k * C / ε ^ 2 * Real.log (1 / δ) := by
  have hδ1 : δ ≤ 1 := hδ.2.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hlog : 1 ≤ Real.log (1 / δ) := by
    have h := Real.log_le_log hδ.1 hδ.2
    rw [Real.log_exp] at h
    simpa only [one_div, Real.log_inv] using (by linarith : 1 ≤ -Real.log δ)
  have heps : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  have hdiv : 1 ≤ C / ε ^ 2 := (one_le_div heps).mpr (by nlinarith [hε.1, hε.2])
  have ha : 1 ≤ C / ε ^ 2 * Real.log (1 / δ) := one_le_mul_of_one_le_of_one_le hdiv hlog
  have h := testingCopies_le k (ε := ε) (by linarith : 0 ≤ C) ⟨hδ.1, hδ1⟩
  calc
    _ ≤ (k : ℝ) * (C / ε ^ 2 * Real.log (1 / δ) + 1) := h
    _ ≤ (k : ℝ) * (2 * (C / ε ^ 2 * Real.log (1 / δ))) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
    _ = _ := by ring

end
end GaussianTesting
