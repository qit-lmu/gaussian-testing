module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberCoherent
public import GaussianTesting.Bosons.PhysicalCoherent
public import GaussianTesting.Bosons.GaussianWaveStates
public import GaussianTesting.GradientFlow.HilbertSpectralGap

@[expose] public section

/-!
# Coherent-state fidelity: Theorem 6.5

Lemma 6.6 supplies the spectral parameter `α = 1/2` for the actual coherent
test. Theorem 3.4 then gives a certainty witness with linear constant four.
Proposition 6.3 identifies its certainty set with the manuscript's independent
displaced-vacuum class. Fidelity is the supremum of absolute overlaps from
Eq. (3.2). This is the manuscript's proof on completed physical tensor spaces.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

/-- Proposition 6.3 identifies the class in Theorem 6.5 with the normalized
certainty set used in the general robustness theorem. -/
theorem coherentWaveStates_eq_certaintyStates (m : ℕ) :
    coherentWaveStates m = certaintyStates (@schrodingerCoherentAcceptance m) := by
  ext φ
  constructor
  · intro hφ
    have hn := norm_eq_one_of_mem_coherentWaveStates hφ
    exact ⟨hn, (schrodingerCoherentAcceptance_eq_one_iff φ hn).mpr hφ⟩
  · rintro ⟨hn, hp⟩
    exact (schrodingerCoherentAcceptance_eq_one_iff φ hn).mp hp

/-- The physical coherent witness in Theorem 6.5. The error's nonnegativity
follows from the probability bound, so only the manuscript's hypotheses are
required. The same witness bounds the squared supremal fidelity. -/
theorem schrodinger_coherent_fidelity_witness {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerCoherentAcceptance ψ) :
    ∃ φ ∈ coherentWaveStates m,
      1 - 4 * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 ∧
      ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity (coherentWaveStates m) ψ ^ 2 := by
  have hτ : 0 ≤ τ := by
    have hprob := (schrodingerCoherentAcceptance_mem_Icc ψ hψ).2
    linarith
  have hne : (certaintyStates (@schrodingerCoherentAcceptance m)).Nonempty := by
    rw [← coherentWaveStates_eq_certaintyStates]
    refine ⟨waveVacuum m, 0, 1, norm_one, ?_⟩
    simp only [weylOperator_zero, one_smul]
  have hspec : spectrum ℂ (threeCopyAverage (schrodingerQ m)) ⊆
      Complex.ofReal '' Set.Icc 0 (1 / 2 : ℝ) ∪ {1} :=
    schrodinger_coherent_spectrum_subset m
  obtain ⟨φ, hφ, _, _, hlin, hfid⟩ :=
    robustness_of_threeCopy_spectrum (schrodingerQ_isAcceptance m)
      (α := 1 / 2) (by norm_num) (by norm_num) hspec hne hψ
  have hφG : φ ∈ coherentWaveStates m := by
    rw [coherentWaveStates_eq_certaintyStates]
    exact hφ
  refine ⟨φ, hφG, ?_, ?_⟩
  · have hC : Cgap (1 / 2) = 4 := by norm_num [Cgap]
    simpa only [hC] using hlin τ hτ hp
  · rw [coherentWaveStates_eq_certaintyStates]
    exact hfid

/-- **Theorem 6.5.** Acceptance at least `1 − τ` by the physical coherent
test implies squared fidelity at least `1 − 4τ` with the displaced-vacuum class. -/
theorem schrodinger_coherent_fidelity {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerCoherentAcceptance ψ) :
    1 - 4 * τ ≤ pureFidelity (coherentWaveStates m) ψ ^ 2 := by
  obtain ⟨_, _, hlin, hfid⟩ := schrodinger_coherent_fidelity_witness ψ hψ hp
  exact hlin.trans hfid

end
end GaussianTesting
