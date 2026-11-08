module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GaussianForward
public import GaussianTesting.Bosons.GaussianPurityReduction
public import GaussianTesting.Bosons.GaussianSymplecticReduction

@[expose] public section

/-!
# Gaussian and coherent certainty: Proposition 6.3

The physical four-copy test accepts exactly the independently defined displaced
symplectic vacuum orbit. The converse uses the manuscript's purity reduction,
Proposition 6.1, symplectic transport to the vacuum, and coherent certainty.
The forward direction uses the manuscript's displaced Gaussian factorization
after the inverse balanced splitter.
-/

namespace GaussianTesting

noncomputable section

/-- The general Gaussian equivalence in Proposition 6.3, for the actual
four-copy accepting projection and the manuscript's independent Gaussian set. -/
theorem schrodingerFourCopyAcceptance_eq_one_iff {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerFourCopyAcceptance ψ = 1 ↔ ψ ∈ gaussianWaveStates m := by
  constructor
  · intro hp
    obtain ⟨u, φ, _, hφ, hfactor⟩ :=
      gaussian_factorization_of_fourCopyAcceptance_one ψ hψ hp
    exact mem_gaussianWaveStates_of_meanZero_factorization ψ u φ hψ hφ hfactor
  · exact schrodingerFourCopyAcceptance_of_mem_gaussianWaveStates

/-- **Proposition 6.3**, both manuscript equivalences on actual Schrödinger
wavefunctions, with only the unit-norm hypothesis. -/
theorem bosonicGaussian_and_coherent_characterization {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    (ψ ∈ gaussianWaveStates m ↔ schrodingerFourCopyAcceptance ψ = 1) ∧
    (ψ ∈ coherentWaveStates m ↔ schrodingerCoherentAcceptance ψ = 1) :=
  ⟨(schrodingerFourCopyAcceptance_eq_one_iff ψ hψ).symm,
    (schrodingerCoherentAcceptance_eq_one_iff ψ hψ).symm⟩

end
end GaussianTesting
