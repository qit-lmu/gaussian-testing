module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SymplecticAction
public import GaussianTesting.Bosons.SchrodingerVacuum

@[expose] public section

/-!
# The Gaussian state sets used by Section 6

The manuscript identifies centered pure Gaussian states with the symplectic
vacuum orbit, general pure Gaussian states with its Weyl displacements, and
coherent states with displaced vacua. We use these independent orbit
characterizations as the definitions on actual Schrödinger wavefunctions.
Unit complex scalars account for the irrelevant global phase of a pure state.

These are the state sets needed by the Section 6 tests. The alternative
quadratic-Hamiltonian definition and an explicit unbounded mean-operator
formulation are not used as definitions or assumed equivalences here.
-/

namespace GaussianTesting

noncomputable section

/-- The manuscript's `𝒢ₘ⁰`: unit-phase symplectic images of the vacuum. -/
def meanZeroGaussianWaveStates (m : ℕ) : Set (WaveSpace m) :=
  {f | ∃ (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (z : ℂ),
    ‖z‖ = 1 ∧ f = z • waveSymplecticUnitary S hS (waveVacuum m)}

/-- The manuscript's `𝒢ₘ`: unit-phase displaced symplectic images of the vacuum. -/
def gaussianWaveStates (m : ℕ) : Set (WaveSpace m) :=
  {f | ∃ (a : WavePhase m) (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (z : ℂ),
    ‖z‖ = 1 ∧ f = z • weylOperator m a (waveSymplecticUnitary S hS (waveVacuum m))}

/-- The manuscript's `𝒞ₘ`: unit-phase displaced vacua. -/
def coherentWaveStates (m : ℕ) : Set (WaveSpace m) :=
  {f | ∃ (a : WavePhase m) (z : ℂ),
    ‖z‖ = 1 ∧ f = z • weylOperator m a (waveVacuum m)}

theorem norm_eq_one_of_mem_meanZeroGaussianWaveStates {m : ℕ} {f : WaveSpace m}
    (hf : f ∈ meanZeroGaussianWaveStates m) : ‖f‖ = 1 := by
  obtain ⟨S,hS,z,hz,rfl⟩ := hf
  rw [norm_smul, hz, LinearIsometryEquiv.norm_map, waveVacuum_norm, one_mul]

theorem norm_eq_one_of_mem_gaussianWaveStates {m : ℕ} {f : WaveSpace m}
    (hf : f ∈ gaussianWaveStates m) : ‖f‖ = 1 := by
  obtain ⟨a,S,hS,z,hz,rfl⟩ := hf
  rw [norm_smul, hz, weylOperator_norm, LinearIsometryEquiv.norm_map, waveVacuum_norm, one_mul]

theorem norm_eq_one_of_mem_coherentWaveStates {m : ℕ} {f : WaveSpace m}
    (hf : f ∈ coherentWaveStates m) : ‖f‖ = 1 := by
  obtain ⟨a,z,hz,rfl⟩ := hf
  rw [norm_smul, hz, weylOperator_norm, waveVacuum_norm, one_mul]

end
end GaussianTesting
