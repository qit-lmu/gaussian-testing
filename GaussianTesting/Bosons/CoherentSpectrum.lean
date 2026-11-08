module

public import GaussianTesting.Bosons.Coherent
public import GaussianTesting.GradientFlow.Spectral

@[expose] public section

/-!
# The spectrum of the three-copy coherent-state test

The exact three-vector Gram calculation identifies the nonzero eigenvalues
on the rotated occupation sectors (`blockSpectrumQ_nonzero`). The cases
`k=0,1,2` and strict bound for `k≥3` give the finite-block polynomial
inequality; summing the orthogonal particle-number blocks then transfers
this spectral gap to the full Fock space. The polynomial is an analytic
assembly device after the manuscript's exact spectral calculation.
-/

namespace GaussianTesting

/-- Lemma 6.6. For any number of modes, the spectrum of the average of the
three pairwise coherent test projections is contained in `[0, 1/2] ∪ {1}`. -/
theorem coherent_spectrum_subset (m : ℕ) :
    spectrum ℂ (Slp (QB_norm_le_one m)) ⊆ Complex.ofReal '' Set.Icc 0 (1 / 2) ∪ {1} := by
  exact (spectrum_gap_iff_quadraticForm_nonneg
    (Slp_nonneg _ (QB_isAcceptance m)) (Slp_norm_le_one _) (1 / 2)).mpr
    (coherent_polynomial_gap m)

end GaussianTesting
