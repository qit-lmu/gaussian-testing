module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CopyKac
public import GaussianTesting.Fermions.GaussianCertainty
public import GaussianTesting.GradientFlow.FiniteHilbert

@[expose] public section

/-!
# Theorem 5.2: fidelity with fermionic Gaussian states

The second-quantized copy action identifies the pair average with the Kac
operator. Theorem 4.1 supplies its spectrum and Theorem 3.4 supplies a
certainty witness through the projective gradient flow. Lemma 5.1 identifies
the certainty class with the independent even/odd Gaussian orbit union.
-/

namespace GaussianTesting

noncomputable section

/-- Lemma 5.1 identifies the Gaussian class with the normalized certainty set. -/
theorem fermionicGaussianStates_eq_certaintyStates (m : ℕ) :
    fermionicGaussianStates m = certaintyStates (accProb (PF m)) := by
  ext ψ
  constructor
  · intro hψ
    have hn := ((mem_fermionicGaussianStates_iff ψ).mp hψ).norm_eq_one
    exact ⟨hn, (fermionicGaussian_iff_accProb hn).mp hψ⟩
  · rintro ⟨hn, hp⟩
    exact (fermionicGaussian_iff_accProb hn).mpr hp

/-- **Theorem 5.2**, with a Gaussian witness and its comparison to the
manuscript's supremal fidelity. Only the acceptance hypothesis is required. -/
theorem fermionic_fidelity_witness {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ accProb (PF m) ψ) :
    ∃ φ ∈ fermionicGaussianStates m,
      1 - 8 * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 ∧
      ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity (fermionicGaussianStates m) ψ ^ 2 := by
  have hτ : 0 ≤ τ := by
    have hprob := accProb_le_one (PF_isAcceptanceProjection m) hψ
    linarith
  have hne : (certaintyStates (accProb (PF m))).Nonempty := by
    refine ⟨fermionVacuum m, norm_fermionVacuum m, ?_⟩
    exact (accProb_PF_eq_one_iff (norm_fermionVacuum m)).mpr lambdaF_tp2_basisState
  obtain ⟨φ, hφ, _, _, hlin, hfid⟩ := finite_robustness_of_spectrum
    (PF_isAcceptanceProjection m) (α := 7 / 12) (by norm_num) (by norm_num)
    (fermionic_spectrum_subset m) hne hψ
  have hφG : φ ∈ fermionicGaussianStates m := by
    rw [fermionicGaussianStates_eq_certaintyStates]
    exact hφ
  refine ⟨φ, hφG, ?_, ?_⟩
  · simpa only [Cgap_seventwelfths] using hlin τ hτ hp
  · rw [fermionicGaussianStates_eq_certaintyStates]
    exact hfid

/-- **Theorem 5.2.** Acceptance at least `1 − τ` gives squared fidelity at
least `1 − 8τ` with the manuscript's fermionic Gaussian class. -/
theorem fermionic_fidelity {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ accProb (PF m) ψ) :
    1 - 8 * τ ≤ pureFidelity (fermionicGaussianStates m) ψ ^ 2 := by
  obtain ⟨_, _, hlin, hfid⟩ := fermionic_fidelity_witness ψ hψ hp
  exact hlin.trans hfid

end
end GaussianTesting
