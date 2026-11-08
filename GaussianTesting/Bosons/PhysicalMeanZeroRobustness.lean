module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerMeanZeroAcceptance
public import GaussianTesting.Bosons.SchrodingerKac
public import GaussianTesting.GradientFlow.HilbertSpectralGap

@[expose] public section

/-!
# Mean-zero Gaussian fidelity: Theorem 6.4

The actual three-copy SO(3) representation identifies the pair average with
the Kac operator. Theorem 4.1 supplies its spectral bound with `α = 7/12`.
Theorem 3.4 then gives a certainty witness with linear constant eight, and
Proposition 6.1 identifies that witness with the symplectic vacuum orbit.
This follows the manuscript proof on completed physical tensor spaces.
-/

namespace GaussianTesting

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

/-- Proposition 6.1 identifies the physical mean-zero class with the
normalized certainty set in Theorem 3.4. -/
theorem meanZeroGaussianWaveStates_eq_certaintyStates (m : ℕ) :
    meanZeroGaussianWaveStates m = certaintyStates (@schrodingerMeanZeroAcceptance m) := by
  ext φ
  constructor
  · intro hφ
    have hn := norm_eq_one_of_mem_meanZeroGaussianWaveStates hφ
    exact ⟨hn, (schrodingerMeanZeroAcceptance_eq_one_iff φ hn).mpr hφ⟩
  · rintro ⟨hn, hp⟩
    exact (schrodingerMeanZeroAcceptance_eq_one_iff φ hn).mp hp

/-- **Theorem 6.4**, including a physical centered Gaussian witness and the
comparison with squared supremal fidelity from Eq. (3.2). -/
theorem schrodinger_meanZero_fidelity_witness {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerMeanZeroAcceptance ψ) :
    ∃ φ ∈ meanZeroGaussianWaveStates m,
      1 - 8 * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 ∧
      ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity (meanZeroGaussianWaveStates m) ψ ^ 2 := by
  have hτ : 0 ≤ τ := by
    have hprob := (schrodingerMeanZeroAcceptance_mem_Icc ψ hψ).2
    linarith
  have hne : (certaintyStates (@schrodingerMeanZeroAcceptance m)).Nonempty := by
    refine ⟨waveVacuum m, waveVacuum_norm m, ?_⟩
    exact (schrodingerMeanZeroAcceptance_eq_one_iff_fixed (waveVacuum m)
      (waveVacuum_norm m)).mpr (schrodingerTensorP0_vacuum m)
  obtain ⟨φ, hφ, _, _, hlin, hfid⟩ :=
    robustness_of_threeCopy_spectrum (schrodingerTensorP0_isAcceptance m)
      (α := 7 / 12) (by norm_num) (by norm_num)
      (schrodinger_meanZero_spectrum_subset m) hne hψ
  have hφG : φ ∈ meanZeroGaussianWaveStates m := by
    rw [meanZeroGaussianWaveStates_eq_certaintyStates]
    exact hφ
  refine ⟨φ, hφG, ?_, ?_⟩
  · have hC : Cgap (7 / 12) = 8 := by norm_num [Cgap]
    simpa only [hC] using hlin τ hτ hp
  · rw [meanZeroGaussianWaveStates_eq_certaintyStates]
    exact hfid

/-- **Theorem 6.4.** Acceptance at least `1 − τ` by the physical mean-zero
test implies squared fidelity at least `1 − 8τ` with centered Gaussian states. -/
theorem schrodinger_meanZero_fidelity {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerMeanZeroAcceptance ψ) :
    1 - 8 * τ ≤ pureFidelity (meanZeroGaussianWaveStates m) ψ ^ 2 := by
  obtain ⟨_, _, hlin, hfid⟩ := schrodinger_meanZero_fidelity_witness ψ hψ hp
  exact hlin.trans hfid

end
end GaussianTesting
