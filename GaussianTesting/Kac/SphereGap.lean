module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereGapBound
public import GaussianTesting.Kac.SphereSpinFour
public import GaussianTesting.Kac.SphereHarmonicQuartic

@[expose] public section

/-!
# The exact spherical Kac gap

This completes the spherical assertion of manuscript Theorem 4.1. The bound
on the orthogonal complement of constants follows the representation argument.
The three degree-four zonal harmonics realize the manuscript's spin-four
matrix with off-diagonal coefficient `3/8`; their nonzero sum attains `7/12`.
Thus the restricted operator has norm `7/12` and the spectral gap is `5/12`.
-/

namespace GaussianTesting.SO3

noncomputable section

/-- The axial functions used for attainment are restrictions of homogeneous harmonic quartics. -/
theorem sphereZonalFour_eq_polynomial (a : Fin 3) (x : Sphere) :
    sphereZonalFour a x =
      (MvPolynomial.eval (fun i => (x : SphereAmbient) i) (zonalFourPolynomial a) : ℂ) := by
  rw [zonalFourPolynomial_eval_sphere]
  rfl

/-- The sum of the three axial degree-four harmonics, in the mean-zero L² subspace. -/
def sphereSpinFourVector : sphereMeanZero :=
  ⟨sphereContinuousToLp sphereSpinFour,
    sphereKacTransition_eigenvector_mem_meanZero (by norm_num) sphereKacTransition_spinFour⟩

theorem sphereSpinFourVector_ne_zero : sphereSpinFourVector ≠ 0 := by
  intro h
  exact sphereSpinFour_toLp_ne_zero (congrArg Subtype.val h)

/-- The manuscript's symmetric spin-four eigenvector attains `7/12` away from constants. -/
theorem sphereMeanZeroKac_spinFour :
    sphereMeanZeroKac sphereSpinFourVector = (7 / 12 : ℂ) • sphereSpinFourVector := by
  apply Subtype.ext
  rw [sphereMeanZeroKac_coe]
  exact sphereKacTransition_spinFour

/-- The upper bound is sharp for the actual spherical transition operator. -/
theorem sphereMeanZeroKac_norm_eq : ‖sphereMeanZeroKac‖ = 7 / 12 := by
  apply le_antisymm sphereMeanZeroKac_norm_le
  have hv : 0 < ‖sphereSpinFourVector‖ := norm_pos_iff.mpr sphereSpinFourVector_ne_zero
  have hb := sphereMeanZeroKac.le_opNorm sphereSpinFourVector
  rw [sphereMeanZeroKac_spinFour, norm_smul] at hb
  norm_num at hb
  change (7 / 12 : ℝ) * ‖sphereSpinFourVector‖ ≤
    ‖sphereMeanZeroKac‖ * ‖sphereSpinFourVector‖ at hb
  nlinarith

/-- The complete spectrum of the mean-zero restriction lies in `[0,7/12]`. -/
theorem sphereMeanZeroKac_spectrum_subset :
    spectrum ℂ sphereMeanZeroKac ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) (7 / 12) := by
  intro z hz
  have hspec := kacAverage_spectrum_subset sphereMeanZeroRepresentation
    (UnitaryRepresentation.continuous_restrict_orbit sphereRepresentation
      continuous_sphereRepresentation_orbit sphereMeanZero sphereMeanZero_invariant) hz
  rcases hspec with h | h
  · exact h
  · have he : z = 1 := Set.mem_singleton_iff.mp h
    have hn := spectrum.norm_le_norm_mul_of_mem hz
    have hi : ‖(1 : sphereMeanZero →L[ℂ] sphereMeanZero)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    rw [he, norm_one] at hn
    have hb : ‖sphereMeanZeroKac‖ * ‖(1 : sphereMeanZero →L[ℂ] sphereMeanZero)‖ ≤ 7 / 12 := by
      calc
        _ ≤ ‖sphereMeanZeroKac‖ * 1 := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
        _ ≤ 7 / 12 := by simpa using sphereMeanZeroKac_norm_le
    linarith

/-- The endpoint `7/12` belongs to the spectrum of the mean-zero restriction. -/
theorem sphereMeanZeroKac_sharp_mem_spectrum :
    (7 / 12 : ℂ) ∈ spectrum ℂ sphereMeanZeroKac := by
  rw [ContinuousLinearMap.spectrum_eq]
  apply Module.End.HasEigenvalue.mem_spectrum
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := sphereSpinFourVector)
  exact ⟨Module.End.mem_eigenspace_iff.mpr sphereMeanZeroKac_spinFour,
    sphereSpinFourVector_ne_zero⟩

/-- The largest nonconstant spherical spectral value is exactly `7/12`. -/
theorem sphereMeanZeroKac_isGreatest_spectrum :
    IsGreatest {r : ℝ | (r : ℂ) ∈ spectrum ℂ sphereMeanZeroKac} (7 / 12) := by
  constructor
  · simpa using sphereMeanZeroKac_sharp_mem_spectrum
  · intro r hr
    obtain ⟨s, hs, he⟩ := sphereMeanZeroKac_spectrum_subset hr
    have hsr : s = r := Complex.ofReal_injective he
    simpa only [hsr] using hs.2

/-- **Theorem 4.1, spherical assertion.** The discrete-time Kac walk on the
sphere has exact spectral gap `5/12` on the orthogonal complement of constants. -/
theorem sphereKac_spectralGap : 1 - ‖sphereMeanZeroKac‖ = 5 / 12 := by
  rw [sphereMeanZeroKac_norm_eq]
  norm_num

end
end GaussianTesting.SO3
