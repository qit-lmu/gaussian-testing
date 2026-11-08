module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.Robustness
public import GaussianTesting.RepeatedTest

@[expose] public section

/-!
# Corollary 5.3: testing fermionic Gaussian states

Repeat the two-outcome measurement with accepting projection `PF m` on fresh
pairs of copies, and accept exactly when every round accepts. Theorem 5.2
gives the one-round rejection bound for the manuscript's Gaussian fidelity;
Lemma 5.1 gives perfect completeness. The independent product law, ceiling
round count, and total number of input copies are explicit.
-/

namespace GaussianTesting

noncomputable section

/-- Theorem 5.2 turns the manuscript's squared-fidelity promise into a
one-round rejection probability of at least `ε²/8`. -/
theorem fermionic_acceptance_le_of_far {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {ε : ℝ}
    (hfar : pureFidelity (fermionicGaussianStates m) ψ ^ 2 ≤ 1 - ε ^ 2) :
    accProb (PF m) ψ ≤ 1 - ε ^ 2 / 8 := by
  have h := fermionic_fidelity ψ hψ (τ := 1 - accProb (PF m) ψ) (by linarith)
  linarith

/-- The independent outcome law for the two-copy measurements in Corollary 5.3.
Each Bernoulli parameter is the Born acceptance probability of `PF m` on
`ψ ⊗ ψ`; distinct rounds use fresh pairs of input copies. -/
def fermionicTestProtocol {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) (ε δ : ℝ) :=
  repeatedTestLaw ⟨accProb (PF m) ψ,
    accProb_nonneg (PF_isAcceptanceProjection m) ψ,
    accProb_le_one (PF_isAcceptanceProjection m) hψ⟩ (testingRounds 8 ε δ)

/-- Two fresh copies per round, with the manuscript's integer round count. -/
def fermionicTestCopies (ε δ : ℝ) : ℕ := 2 * testingRounds 8 ε δ

/-- Independence gives the exact probability that every pair test accepts. -/
theorem fermionicTestProtocol_acceptance {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1)
    (ε δ : ℝ) :
    (fermionicTestProtocol ψ hψ ε δ).real (repeatedTestAccepts (testingRounds 8 ε δ)) =
      accProb (PF m) ψ ^ testingRounds 8 ε δ :=
  repeatedTest_acceptance _ _

/-- The protocol rejects precisely when at least one pair test rejects. -/
theorem fermionicTestProtocol_rejection {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1)
    (ε δ : ℝ) :
    (fermionicTestProtocol ψ hψ ε δ).real (repeatedTestAccepts (testingRounds 8 ε δ))ᶜ =
      1 - accProb (PF m) ψ ^ testingRounds 8 ε δ :=
  repeatedTest_rejection _ _

/-- **Corollary 5.3.** The repeated pair-test protocol has perfect completeness
and rejects with probability at least `1−δ` whenever squared Gaussian fidelity
is at most `1−ε²`. It uses exactly `2·ceil((8/ε²) log(1/δ))` input copies.
The bound retaining the ceiling is valid for every `ε, δ ∈ (0,1)`. -/
theorem fermionic_testing {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    let n := testingRounds 8 ε δ
    let μ := fermionicTestProtocol ψ hψ ε δ
    (ψ ∈ fermionicGaussianStates m → μ.real (repeatedTestAccepts n) = 1) ∧
    (pureFidelity (fermionicGaussianStates m) ψ ^ 2 ≤ 1 - ε ^ 2 →
      μ.real (repeatedTestAccepts n) ≤ δ ∧
      1 - δ ≤ μ.real (repeatedTestAccepts n)ᶜ) ∧
    fermionicTestCopies ε δ = 2 * n ∧
    (fermionicTestCopies ε δ : ℝ) ≤ 16 / ε ^ 2 * Real.log (1 / δ) + 2 := by
  dsimp only
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro hmem
    rw [fermionicTestProtocol_acceptance, (fermionicGaussian_iff_accProb hψ).mp hmem,
      one_pow]
  · intro hfar
    have hs := repeatedTest_soundness
      (p := ⟨accProb (PF m) ψ, accProb_nonneg (PF_isAcceptanceProjection m) ψ,
        accProb_le_one (PF_isAcceptanceProjection m) hψ⟩)
      (by norm_num : (0 : ℝ) < 8) hε.1 hδ.1
      (fermionic_acceptance_le_of_far ψ hψ hfar) (testingRounds_sufficient 8 ε δ)
    refine ⟨hs, ?_⟩
    rw [fermionicTestProtocol_rejection]
    rw [repeatedTest_acceptance] at hs
    linarith
  · have h := testingCopies_le 2 (C := 8) (ε := ε) (by norm_num) ⟨hδ.1, hδ.2.le⟩
    change ((2 * testingRounds 8 ε δ : ℕ) : ℝ) ≤ _
    convert h using 1
    push_cast
    ring

/-- An explicit constant for the manuscript's asymptotic sample complexity.
For `δ ≤ e⁻¹`, at most `32 ε⁻² log(1/δ)` copies suffice, independently of
the number of modes. The preceding corollary retains the ceiling for all `δ`. -/
theorem fermionicTestCopies_le_rate {ε δ : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (Real.exp (-1))) :
    (fermionicTestCopies ε δ : ℝ) ≤ 32 / ε ^ 2 * Real.log (1 / δ) := by
  simpa only [fermionicTestCopies, Nat.cast_ofNat, show (2 : ℝ) * 2 * 8 = 32 by norm_num]
    using testingCopies_le_rate 2 (C := 8) (by norm_num) ⟨hε.1, hε.2.le⟩ hδ

end
end GaussianTesting
