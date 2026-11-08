module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CovarianceOccupation
public import GaussianTesting.Fermions.GaussianTestInvariance
public import GaussianTesting.Fermions.SkewNormalForm

@[expose] public section

/-!
# Lemma 5.1: the fermionic certainty states

The Gaussian class is the independently defined union of the even and odd
SO(2m) implementer orbits. The reverse implication follows the manuscript:
the covariance norm identity, general real antisymmetric normal form,
Gaussian transport, and saturation of the occupation expectations. No parity
hypothesis is imposed, and the construction also includes zero modes.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- The saturated covariance norm in Eq. (5.3), obtained from the kernel condition. -/
theorem sum_sq_covMat_of_lambdaF_eq_zero {ψ : HF m} (hψ : ‖ψ‖ = 1)
    (hΛ : lambdaF m (tp2 ψ ψ) = 0) :
    (∑ a, ∑ b, covMat ψ a b ^ 2) = (2 * m : ℝ) := by
  have h := congrArg Complex.re (norm_lambdaF_tp2 hψ)
  rw [hΛ] at h
  simp only [inner_zero_left, Complex.zero_re, Complex.ofReal_re] at h
  linarith

/-- Lemma 5.1, the manuscript's covariance-normal-form implication to the
independently defined even/odd Gaussian orbits. -/
theorem fermionicGaussian_of_lambdaF_eq_zero {ψ : HF m} (hψ : ‖ψ‖ = 1)
    (hΛ : lambdaF m (tp2 ψ ψ) = 0) : ψ ∈ fermionicGaussianStates m := by
  classical
  obtain ⟨R, c, hc⟩ := exists_specialOrthogonal_skewNormalForm
    (Matrix.of (covMat ψ)) (covMat_antisymm ψ)
  let U := gaussianImplementer R
  have hU : ImplementsMajoranaRotation R U := gaussianImplementer_implements R
  have hφ : ‖U.symm ψ‖ = 1 := by simpa using hψ
  have hblock : Matrix.of (covMat (U.symm ψ)) = skewBlockMatrix c :=
    (hU.covMat_symm ψ).trans hc
  have hnorm : (∑ a, ∑ b, covMat (U.symm ψ) a b ^ 2) = (2 * m : ℝ) :=
    (hU.sum_sq_covMat_symm ψ).trans (sum_sq_covMat_of_lambdaF_eq_zero hψ hΛ)
  obtain ⟨x, z, hz, hx⟩ := exists_phase_basis_of_covMat_skewBlockMatrix hφ hblock hnorm
  have horbit : ψ ∈ fermionicGaussianOrbit x := by
    refine ⟨U * fermionPhaseEquiv z hz,
      (gaussianUnitaryGroup m).mul_mem ⟨R, hU⟩
        (planeUnitaryGroup_le_gaussianUnitaryGroup
          (fermionPhaseEquiv_mem_planeUnitaryGroup z hz)), ?_⟩
    change U (z • EuclideanSpace.single x 1) = ψ
    rw [← hx, U.apply_symm_apply]
  rcases neg_one_pow_eq_or ℂ (Finset.univ.filter fun k => x k).card with hp | hp
  · exact Or.inl ⟨x, hp, horbit⟩
  · exact Or.inr ⟨x, hp, horbit⟩

/-- **Lemma 5.1**, (i) iff (ii), for any pure input with no parity restriction. -/
theorem fermionicGaussian_iff_lambdaF {ψ : HF m} (hψ : ‖ψ‖ = 1) :
    ψ ∈ fermionicGaussianStates m ↔ lambdaF m (tp2 ψ ψ) = 0 :=
  ⟨fermionicGaussian_lambdaF_eq_zero, fermionicGaussian_of_lambdaF_eq_zero hψ⟩

/-- **Lemma 5.1**, (i) iff (iii), with the manuscript's acceptance probability. -/
theorem fermionicGaussian_iff_accProb {ψ : HF m} (hψ : ‖ψ‖ = 1) :
    ψ ∈ fermionicGaussianStates m ↔ accProb (PF m) ψ = 1 := by
  rw [fermionicGaussian_iff_lambdaF hψ, accProb_PF_eq_one_iff hψ]

end
end GaussianTesting
