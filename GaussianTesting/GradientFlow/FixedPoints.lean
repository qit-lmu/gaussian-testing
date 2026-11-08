module

public import GaussianTesting.GradientFlow.HilbertGradientBound
public import GaussianTesting.Fidelity

@[expose] public section

/-!
# Certainty states and fixed tensor cubes

After Lemma 3.2 the manuscript identifies the elementary tensor cubes fixed by
the three-copy average. A nonempty certainty set therefore gives an eigenvector
at the upper endpoint of its spectrum.
-/

namespace GaussianTesting

open scoped InnerProductSpace TensorProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

omit [CompleteSpace H] in
private theorem norm_unit_cube {ψ : H} (hψ : ‖ψ‖ = 1) :
    ‖hilbertTmul ψ (hilbertTmul ψ ψ)‖ = 1 := by
  change ‖((ψ ⊗ₜ[ℂ] hilbertTmul ψ ψ : H ⊗[ℂ] HilbertSquare H) :
    UniformSpace.Completion (H ⊗[ℂ] HilbertSquare H))‖ = 1
  rw [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, hψ, one_mul]
  change ‖((ψ ⊗ₜ[ℂ] ψ : H ⊗[ℂ] H) : UniformSpace.Completion (H ⊗[ℂ] H))‖ = 1
  simp [hψ]

/-- For unit `ψ`, the three-copy average fixes `ψ⊗ψ⊗ψ` exactly when the test
accepts `ψ` with probability one. -/
theorem threeCopyAverage_fixed_iff_accProb_eq_one (hP : (hilbertTensorSquare H).IsAcceptance P)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    let Ψ := hilbertTmul ψ (hilbertTmul ψ ψ)
    threeCopyAverage P Ψ = Ψ ↔ (hilbertTensorSquare H).accProbA P ψ = 1 := by
  let Ψ := hilbertTmul ψ (hilbertTmul ψ ψ)
  have hnorm : ‖Ψ‖ = 1 := norm_unit_cube hψ
  have hmoment : ⟪Ψ, threeCopyAverage P Ψ⟫_ℂ = ((hilbertTensorSquare H).accProbA P ψ : ℂ) :=
    (threeCopyAverage_moments hP hψ).1
  constructor
  · intro hfix
    change threeCopyAverage P Ψ = Ψ at hfix
    rw [hfix, inner_self_eq_norm_sq_to_K, hnorm] at hmoment
    simpa using (congrArg Complex.re hmoment).symm
  · intro hacc
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℂ)
    · simpa only [one_mul] using
        (threeCopyAverage P).le_of_opNorm_le (threeCopyAverage_positive_contraction hP).2 Ψ
    · change RCLike.re ⟪threeCopyAverage P Ψ, Ψ⟫_ℂ = ‖Ψ‖ ^ 2
      rw [inner_re_symm, hmoment, hacc, hnorm]
      norm_num

/-- A certainty state supplies a nonzero tensor cube with eigenvalue one. -/
theorem threeCopyAverage_hasEigenvalue_one (hP : (hilbertTensorSquare H).IsAcceptance P)
    (hne : (certaintyStates ((hilbertTensorSquare H).accProbA P)).Nonempty) :
    Module.End.HasEigenvalue (threeCopyAverage P).toLinearMap (1 : ℂ) := by
  obtain ⟨ψ, hψ, hacc⟩ := hne
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := hilbertTmul ψ (hilbertTmul ψ ψ))
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    rw [one_smul]
    exact (threeCopyAverage_fixed_iff_accProb_eq_one hP hψ).mpr hacc
  · intro hzero
    simpa [hzero] using norm_unit_cube hψ

/-- The complex spectrum of the three-copy average is contained in the real interval
`[0,1]`. In particular the eigenvalue one of a test with a certainty state is maximal. -/
theorem threeCopyAverage_spectrum_subset_unitInterval (hP : (hilbertTensorSquare H).IsAcceptance P) :
    spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hpos, hnorm⟩ := threeCopyAverage_positive_contraction hP
  have hreal : Complex.ofReal '' spectrum ℝ (threeCopyAverage P) = spectrum ℂ (threeCopyAverage P) :=
    (IsSelfAdjoint.of_nonneg hpos).spectrumRestricts.algebraMap_image
  rw [← hreal]
  exact Set.image_mono (real_spectrum_subset_unitInterval hpos hnorm)

/-- When the certainty set is nonempty, one is the largest real eigenvalue of the average. -/
theorem threeCopyAverage_isGreatest_eigenvalue (hP : (hilbertTensorSquare H).IsAcceptance P)
    (hne : (certaintyStates ((hilbertTensorSquare H).accProbA P)).Nonempty) :
    IsGreatest {r : ℝ | Module.End.HasEigenvalue (threeCopyAverage P).toLinearMap (r : ℂ)} 1 := by
  refine ⟨by simpa using threeCopyAverage_hasEigenvalue_one hP hne, ?_⟩
  intro r hr
  obtain ⟨v, hv, hv0⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hr
  have he : threeCopyAverage P v = (r : ℂ) • v := Module.End.mem_eigenspace_iff.mp hv
  have hbound := (threeCopyAverage P).le_of_opNorm_le (threeCopyAverage_positive_contraction hP).2 v
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hbound
  exact (le_abs_self r).trans ((mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv0)).mp hbound)

end GaussianTesting
