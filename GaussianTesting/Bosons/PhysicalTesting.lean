module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PhysicalMeanZeroRobustness
public import GaussianTesting.Bosons.PhysicalGeneralRobustness
public import GaussianTesting.Bosons.PhysicalGaussian
public import GaussianTesting.RepeatedTest

@[expose] public section

/-!
# Physical bosonic testing protocols: Corollary 6.8

Repeat the appropriate physical measurement on independent fresh copy blocks
and accept precisely when every round accepts. The three physical fidelity
theorems give the one-round rejection bound. The product probability law,
integer ceiling, perfect completeness, and total copy counts are explicit.
-/

namespace GaussianTesting

noncomputable section

/-- The three state classes and measurements in Corollary 6.8. -/
inductive BosonicTestKind
  | gaussian
  | meanZero
  | coherent

/-- The number of fresh input copies consumed in one measurement round. -/
def BosonicTestKind.copiesPerRound : BosonicTestKind → ℕ
  | .gaussian => 4
  | .meanZero => 2
  | .coherent => 2

/-- The constants in Theorems 6.7, 6.4, and 6.5, respectively. -/
def BosonicTestKind.fidelityConstant : BosonicTestKind → ℝ
  | .gaussian => 48
  | .meanZero => 8
  | .coherent => 4

theorem BosonicTestKind.fidelityConstant_pos (k : BosonicTestKind) :
    0 < k.fidelityConstant := by cases k <;> norm_num [fidelityConstant]

def BosonicTestKind.stateClass (k : BosonicTestKind) (m : ℕ) : Set (WaveSpace m) :=
  match k with
  | .gaussian => gaussianWaveStates m
  | .meanZero => meanZeroGaussianWaveStates m
  | .coherent => coherentWaveStates m

/-- The Born acceptance probability of the indicated physical measurement. -/
def BosonicTestKind.acceptance (k : BosonicTestKind) {m : ℕ} (ψ : WaveSpace m) : ℝ :=
  match k with
  | .gaussian => schrodingerFourCopyAcceptance ψ
  | .meanZero => schrodingerMeanZeroAcceptance ψ
  | .coherent => schrodingerCoherentAcceptance ψ

theorem BosonicTestKind.acceptance_mem_Icc (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) : k.acceptance ψ ∈ Set.Icc (0 : ℝ) 1 := by
  cases k with
  | gaussian =>
    obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ (WaveSpace m)
    obtain ⟨_, c, _⟩ := exists_hilbertBasis ℂ (SchrodingerSpace m)
    exact schrodingerFourCopyAcceptance_mem_Icc b c ψ hψ
  | meanZero => exact schrodingerMeanZeroAcceptance_mem_Icc ψ hψ
  | coherent => exact schrodingerCoherentAcceptance_mem_Icc ψ hψ

theorem BosonicTestKind.acceptance_eq_one (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) (hmem : ψ ∈ k.stateClass m) :
    k.acceptance ψ = 1 := by
  cases k with
  | gaussian => exact (schrodingerFourCopyAcceptance_eq_one_iff ψ hψ).mpr hmem
  | meanZero => exact (schrodingerMeanZeroAcceptance_eq_one_iff ψ hψ).mpr hmem
  | coherent => exact (schrodingerCoherentAcceptance_eq_one_iff ψ hψ).mpr hmem

/-- The three physical fidelity results in a common interface. -/
theorem BosonicTestKind.fidelity (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ} (hp : 1 - τ ≤ k.acceptance ψ) :
    1 - k.fidelityConstant * τ ≤ pureFidelity (k.stateClass m) ψ ^ 2 := by
  cases k with
  | gaussian => exact schrodinger_gaussian_fidelity ψ hψ hp
  | meanZero => exact schrodinger_meanZero_fidelity ψ hψ hp
  | coherent => exact schrodinger_coherent_fidelity ψ hψ hp

/-- A squared-fidelity deficit `ε²` forces a one-round rejection probability
at least `ε²/C`. This uses the manuscript's supremal fidelity itself. -/
theorem BosonicTestKind.acceptance_le_of_far (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {ε : ℝ}
    (hfar : pureFidelity (k.stateClass m) ψ ^ 2 ≤ 1 - ε ^ 2) :
    k.acceptance ψ ≤ 1 - ε ^ 2 / k.fidelityConstant := by
  have h := k.fidelity ψ hψ (τ := 1 - k.acceptance ψ) (by linarith)
  have hd : ε ^ 2 / k.fidelityConstant ≤ 1 - k.acceptance ψ :=
    (div_le_iff₀ k.fidelityConstant_pos).mpr (by nlinarith)
  linarith

/-- The independent fresh-copy protocol for a chosen class and unit input. -/
def bosonicTestProtocol (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) (ε δ : ℝ) :=
  repeatedTestLaw ⟨k.acceptance ψ, k.acceptance_mem_Icc ψ hψ⟩
    (testingRounds k.fidelityConstant ε δ)

/-- **Corollary 6.8.** The explicit product protocol has perfect completeness,
soundness error at most `δ` for squared fidelity at most `1−ε²`, and consumes
`k·ceil(C/ε² log(1/δ))` copies, with `k = 4,2,2` and `C = 48,8,4`.
The bound including the ceiling is valid throughout the manuscript's range. -/
theorem bosonic_physical_testing (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    let n := testingRounds k.fidelityConstant ε δ
    let μ := bosonicTestProtocol k ψ hψ ε δ
    (ψ ∈ k.stateClass m → μ.real (repeatedTestAccepts n) = 1) ∧
    (pureFidelity (k.stateClass m) ψ ^ 2 ≤ 1 - ε ^ 2 →
      μ.real (repeatedTestAccepts n) ≤ δ ∧
      1 - δ ≤ μ.real (repeatedTestAccepts n)ᶜ) ∧
    ((k.copiesPerRound * n : ℕ) : ℝ) ≤
      k.copiesPerRound * (k.fidelityConstant / ε ^ 2 * Real.log (1 / δ) + 1) := by
  dsimp only
  refine ⟨?_, ?_, testingCopies_le k.copiesPerRound k.fidelityConstant_pos.le
    ⟨hδ.1, hδ.2.le⟩⟩
  · intro hmem
    change (repeatedTestLaw _ _).real _ = _
    rw [repeatedTest_acceptance]
    simp only [k.acceptance_eq_one ψ hψ hmem, one_pow]
  · intro hfar
    have hs := repeatedTest_soundness
      (p := ⟨k.acceptance ψ, k.acceptance_mem_Icc ψ hψ⟩)
      k.fidelityConstant_pos hε.1 hδ.1
      (k.acceptance_le_of_far ψ hψ hfar)
      (testingRounds_sufficient k.fidelityConstant ε δ)
    refine ⟨hs, ?_⟩
    change 1 - δ ≤ (repeatedTestLaw _ _).real (repeatedTestAccepts _)ᶜ
    rw [repeatedTest_rejection]
    rw [repeatedTest_acceptance] at hs
    linarith

end
end GaussianTesting
