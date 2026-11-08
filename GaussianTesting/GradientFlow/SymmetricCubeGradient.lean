module

public import GaussianTesting.GradientFlow.SymmetricCube

@[expose] public section

/-!
# Lemma 3.3 from the spectrum on the symmetric tensor cube

The footnote immediately before Lemma 3.3 only requires the spectral gap on
`Sym³(H)`. The three-copy average preserves this closed subspace, and its
restriction has the same two moments on `ψ ⊗ ψ ⊗ ψ`. The proof is therefore
the manuscript's spectral-polynomial argument on the restricted operator.
-/

namespace GaussianTesting

noncomputable section
open scoped InnerProductSpace

set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 4

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- The three-copy average restricted to the completed symmetric tensor cube. -/
def symmetricThreeCopyAverage (hP : (hilbertTensorSquare H).IsAcceptance P) :
    symmetricCube H →L[ℂ] symmetricCube H :=
  (threeCopyAverage P).restrict (threeCopyAverage_maps_symmetricCube hP)

omit [CompleteSpace H] in
@[simp] theorem coe_symmetricThreeCopyAverage
    (hP : (hilbertTensorSquare H).IsAcceptance P) (v : symmetricCube H) :
    (symmetricThreeCopyAverage hP v : HilbertCube H) = threeCopyAverage P v := rfl

/-- Restricting the three-copy average to `Sym³(H)` preserves positivity and contractivity. -/
theorem symmetricThreeCopyAverage_positive_contraction
    (hP : (hilbertTensorSquare H).IsAcceptance P) :
    0 ≤ symmetricThreeCopyAverage hP ∧ ‖symmetricThreeCopyAverage hP‖ ≤ 1 := by
  obtain ⟨hpos, hnorm⟩ := threeCopyAverage_positive_contraction hP
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp hpos
  constructor
  · apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    exact ⟨fun x y => hp.isSymmetric x y, fun x => hp.2 x⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    exact (threeCopyAverage P).le_of_opNorm_le hnorm x

/-- Three identical copies, regarded as a vector in the symmetric tensor cube. -/
def symmetricTensorCube (ψ : H) : symmetricCube H :=
  ⟨hilbertTmul ψ (hilbertTmul ψ ψ), hilbertTmul_mem_symmetricCube ψ⟩

/-- Lemma 3.2's two moments are unchanged on restricting to the symmetric tensor cube. -/
theorem symmetricThreeCopyAverage_moments
    (hP : (hilbertTensorSquare H).IsAcceptance P) {ψ : H} (hψ : ‖ψ‖ = 1) :
    let Ψ := symmetricTensorCube ψ
    let S := symmetricThreeCopyAverage hP
    let p := (hilbertTensorSquare H).accProbA P ψ
    let q := (hilbertTensorSquare H).qProbA P ψ
    ⟪Ψ, S Ψ⟫_ℂ = (p : ℂ) ∧
      ⟪Ψ, S (S Ψ)⟫_ℂ = (((p + 2 * q) / 3 : ℝ) : ℂ) :=
  threeCopyAverage_moments hP hψ

/-- The moment bound of Lemma 3.3 needs the gap only on `Sym³(H)`, as stated in its footnote. -/
theorem lojasiewiczData_of_symmetricThreeCopy_spectrum
    (hP : (hilbertTensorSquare H).IsAcceptance P) {α : ℝ}
    (hspec : spectrum ℂ (symmetricThreeCopyAverage hP) ⊆
      Complex.ofReal '' Set.Icc 0 α ∪ {1}) :
    (hilbertTensorSquare H).LojasiewiczData P α := by
  intro ψ hψ
  obtain ⟨hpos, hnorm⟩ := symmetricThreeCopyAverage_positive_contraction hP
  obtain ⟨h₁, h₂⟩ := symmetricThreeCopyAverage_moments hP hψ
  have hunit : ⟪symmetricTensorCube ψ, symmetricTensorCube ψ⟫_ℂ = 1 := by
    change ⟪hilbertTmul ψ (hilbertTmul ψ ψ), hilbertTmul ψ (hilbertTmul ψ ψ)⟫_ℂ = 1
    rw [inner_hilbertTmul, inner_hilbertTmul, inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hpoly := (spectrum_gap_iff_quadraticForm_nonneg hpos hnorm α).mp hspec
    (symmetricTensorCube ψ)
  rw [h₂, h₁, hunit, mul_one] at hpoly
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, mul_zero, sub_zero] at hpoly
  nlinarith

/-- Lemma 3.3 with the weaker symmetric-cube spectral hypothesis from its preceding footnote. -/
theorem norm_gradAcc_sq_ge_of_symmetricThreeCopy_spectrum
    (hP : (hilbertTensorSquare H).IsAcceptance P) {α : ℝ} (_hα : α ∈ Set.Icc 0 1)
    (hspec : spectrum ℂ (symmetricThreeCopyAverage hP) ⊆
      Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    16 * ((hilbertTensorSquare H).accProbA P ψ - 3 / 2 * α) *
      (1 - (hilbertTensorSquare H).accProbA P ψ) ≤
      ‖(hilbertTensorSquare H).gradAccA P ψ‖ ^ 2 := by
  rw [(hilbertTensorSquare H).norm_gradAccA_sq hP hψ]
  have hq := lojasiewiczData_of_symmetricThreeCopy_spectrum hP hspec ψ hψ
  nlinarith

end
end GaussianTesting
