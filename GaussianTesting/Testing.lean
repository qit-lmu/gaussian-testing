module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.Testing
public import GaussianTesting.Bosons.PhysicalTesting
public import GaussianTesting.TraceDistance

@[expose] public section

/-!
# Theorem 1.1: testing Gaussianity with constant sample complexity

The introductory theorem uses a bound on the overlap with every Gaussian
state. The corollaries use the supremal class fidelity. The equivalence of
these promises gives the explicit protocols and copy counts stated here.
The rank-one trace-norm identity gives the manuscript's equivalent
trace-distance interpretation, using the same measurements.
-/

namespace GaussianTesting

noncomputable section

theorem fermionicGaussianStates_nonempty (m : ℕ) : (fermionicGaussianStates m).Nonempty := by
  refine ⟨EuclideanSpace.single (fun _ => false) 1,
    (mem_fermionicGaussianStates_iff _).mpr ?_⟩
  simpa using IsGaussian.basis (fun _ : Fin m => false) 1 (by simp)

theorem BosonicTestKind.stateClass_unit (k : BosonicTestKind) {m : ℕ} {φ : WaveSpace m}
    (hφ : φ ∈ k.stateClass m) : ‖φ‖ = 1 := by
  cases k with
  | gaussian => exact norm_eq_one_of_mem_gaussianWaveStates hφ
  | meanZero => exact norm_eq_one_of_mem_meanZeroGaussianWaveStates hφ
  | coherent => exact norm_eq_one_of_mem_coherentWaveStates hφ

theorem BosonicTestKind.stateClass_nonempty (k : BosonicTestKind) (m : ℕ) :
    (k.stateClass m).Nonempty := by
  have hS : (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) ∈
      Matrix.symplecticGroup (Fin m) ℝ := (Matrix.symplecticGroup (Fin m) ℝ).one_mem
  cases k with
  | gaussian =>
    refine ⟨weylOperator m 0 (waveSymplecticUnitary 1 hS (waveVacuum m)),
      0, 1, hS, 1, by simp, ?_⟩
    simp
  | meanZero =>
    refine ⟨waveSymplecticUnitary 1 hS (waveVacuum m), 1, hS, 1, by simp, ?_⟩
    simp
  | coherent =>
    refine ⟨weylOperator m 0 (waveVacuum m), 0, 1, by simp, ?_⟩
    simp

/-- **Theorem 1.1, fermions.** The repeated Bell pair-test protocol has perfect
completeness and rejects with probability at least `1−δ` under the paper's
pointwise squared-overlap promise. The exact copy count includes the ceiling. -/
theorem fermionic_gaussian_testing {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    let n := testingRounds 8 ε δ
    let μ := fermionicTestProtocol ψ hψ ε δ
    (ψ ∈ fermionicGaussianStates m → μ.real (repeatedTestAccepts n) = 1) ∧
    ((∀ φ ∈ fermionicGaussianStates m, ‖inner ℂ ψ φ‖ ^ 2 ≤ 1 - ε ^ 2) →
      μ.real (repeatedTestAccepts n) ≤ δ ∧
      1 - δ ≤ μ.real (repeatedTestAccepts n)ᶜ) ∧
    fermionicTestCopies ε δ = 2 * n ∧
    (fermionicTestCopies ε δ : ℝ) ≤ 16 / ε ^ 2 * Real.log (1 / δ) + 2 := by
  obtain ⟨hc, hs, hn, hb⟩ := fermionic_testing ψ hψ hε hδ
  refine ⟨hc, ?_, hn, hb⟩
  intro hfar
  exact hs ((pureFidelity_sq_le_iff (fermionicGaussianStates_nonempty m)
    (fun φ hφ => ((mem_fermionicGaussianStates_iff φ).mp hφ).norm_eq_one) _).mpr hfar)

/-- **Theorem 1.1, bosons.** The general Gaussian test uses fresh blocks of
four copies. The same statement covers the manuscript's mean-zero Gaussian
and coherent tests, which use fresh pairs. The promise is pointwise overlap
with the independently defined physical state class. -/
theorem bosonic_gaussian_testing (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    let n := testingRounds k.fidelityConstant ε δ
    let μ := bosonicTestProtocol k ψ hψ ε δ
    (ψ ∈ k.stateClass m → μ.real (repeatedTestAccepts n) = 1) ∧
    ((∀ φ ∈ k.stateClass m, ‖inner ℂ ψ φ‖ ^ 2 ≤ 1 - ε ^ 2) →
      μ.real (repeatedTestAccepts n) ≤ δ ∧
      1 - δ ≤ μ.real (repeatedTestAccepts n)ᶜ) ∧
    ((k.copiesPerRound * n : ℕ) : ℝ) ≤
      k.copiesPerRound * (k.fidelityConstant / ε ^ 2 * Real.log (1 / δ) + 1) := by
  obtain ⟨hc, hs, hb⟩ := bosonic_physical_testing k ψ hψ hε hδ
  refine ⟨hc, ?_, hb⟩
  intro hfar
  exact hs ((pureFidelity_sq_le_iff (k.stateClass_nonempty m)
    (fun _ hφ => k.stateClass_unit hφ) _).mpr hfar)

/-- **Theorem 1.1, fermionic trace-distance formulation.** Distance at least
`ε` from every pure Gaussian state gives rejection probability at least
`1−δ`, with the same two-copy rounds and mode-independent copy bound. -/
theorem fermionic_gaussian_testing_traceDistance {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1)
    {ε δ : ℝ} (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    let n := testingRounds 8 ε δ
    let μ := fermionicTestProtocol ψ hψ ε δ
    (ψ ∈ fermionicGaussianStates m → μ.real (repeatedTestAccepts n) = 1) ∧
    ((∀ φ ∈ fermionicGaussianStates m, ε ≤ pureStateTraceDistance ψ φ) →
      μ.real (repeatedTestAccepts n) ≤ δ ∧
      1 - δ ≤ μ.real (repeatedTestAccepts n)ᶜ) ∧
    fermionicTestCopies ε δ = 2 * n ∧
    (fermionicTestCopies ε δ : ℝ) ≤ 16 / ε ^ 2 * Real.log (1 / δ) + 2 := by
  obtain ⟨hc, hs, hn, hb⟩ := fermionic_gaussian_testing ψ hψ hε hδ
  refine ⟨hc, ?_, hn, hb⟩
  intro hfar
  apply hs
  intro φ hφ
  exact (le_pureStateTraceDistance_iff ψ φ hψ
    ((mem_fermionicGaussianStates_iff φ).mp hφ).norm_eq_one hε.1.le).mp (hfar φ hφ)

/-- **Theorem 1.1, bosonic trace-distance formulation.** The general,
mean-zero, and coherent tests use the same physical measurements and exact
integer counts as Corollary 6.8, now with the trace-distance promise. -/
theorem bosonic_gaussian_testing_traceDistance (k : BosonicTestKind) {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    let n := testingRounds k.fidelityConstant ε δ
    let μ := bosonicTestProtocol k ψ hψ ε δ
    (ψ ∈ k.stateClass m → μ.real (repeatedTestAccepts n) = 1) ∧
    ((∀ φ ∈ k.stateClass m, ε ≤ pureStateTraceDistance ψ φ) →
      μ.real (repeatedTestAccepts n) ≤ δ ∧
      1 - δ ≤ μ.real (repeatedTestAccepts n)ᶜ) ∧
    ((k.copiesPerRound * n : ℕ) : ℝ) ≤
      k.copiesPerRound * (k.fidelityConstant / ε ^ 2 * Real.log (1 / δ) + 1) := by
  obtain ⟨hc, hs, hb⟩ := bosonic_gaussian_testing k ψ hψ hε hδ
  refine ⟨hc, ?_, hb⟩
  intro hfar
  apply hs
  intro φ hφ
  exact (le_pureStateTraceDistance_iff ψ φ hψ (k.stateClass_unit hφ) hε.1.le).mp (hfar φ hφ)

end
end GaussianTesting
