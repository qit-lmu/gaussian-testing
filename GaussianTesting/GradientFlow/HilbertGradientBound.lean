module

public import GaussianTesting.GradientFlow.HilbertMoments
public import GaussianTesting.GradientFlow.Spectral
public import GaussianTesting.GradientFlow.Abstract

@[expose] public section

/-!
# Moments and the gradient bound on a Hilbert tensor cube

Lemmas 3.2 and 3.3 of the manuscript. The pair operators are constructed on
the completed tensor cube by tensoring the test with the identity and permuting
factors. A Hilbert basis supplies coordinates for evaluating their moments.
The public statements below take only the Hilbert space and the test projection.
-/

namespace GaussianTesting

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

private def chosenHilbertBasis (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : HilbertBasis ↥((exists_hilbertBasis ℂ H).choose : Set H) ℂ H :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ H))

/-- The average of the three pair operators on the completed tensor cube, Eq. (3.6). -/
def threeCopyAverage (P : HilbertSquare H →L[ℂ] HilbertSquare H) : HilbertCube H →L[ℂ] HilbertCube H :=
  (3 : ℂ)⁻¹ • (threeCopyPair12 P + threeCopyPair13 P + threeCopyPair23 P)

omit [CompleteSpace H] in
/-- Product coordinates give the same average for every Hilbert basis. -/
theorem threeCopyAverage_eq {ι : Type*} (e : H ≃ₗᵢ[ℂ] L2 ι)
    (hP : (hilbertTensorSquare H).IsAcceptance P) :
    threeCopyAverage P = hilbertAverage e hP :=
  (hilbertAverage_eq_threeCopyPairs e hP).symm

/-- The average of the three pair projections is a positive contraction. -/
theorem threeCopyAverage_positive_contraction (hP : (hilbertTensorSquare H).IsAcceptance P) :
    0 ≤ threeCopyAverage P ∧ ‖threeCopyAverage P‖ ≤ 1 := by
  rw [threeCopyAverage_eq (chosenHilbertBasis H).repr hP]
  exact ⟨hilbertAverage_nonneg _ hP, hilbertAverage_norm_le_one _ hP⟩

/-- Lemma 3.2. The expectations of the average and its square on three identical copies. -/
theorem threeCopyAverage_moments (hP : (hilbertTensorSquare H).IsAcceptance P)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    let Ψ := hilbertTmul ψ (hilbertTmul ψ ψ)
    let S := threeCopyAverage P
    let p := (hilbertTensorSquare H).accProbA P ψ
    let q := (hilbertTensorSquare H).qProbA P ψ
    ⟪Ψ, S Ψ⟫_ℂ = (p : ℂ) ∧ ⟪Ψ, S (S Ψ)⟫_ℂ = (((p + 2 * q) / 3 : ℝ) : ℂ) := by
  dsimp only
  rw [threeCopyAverage_eq (chosenHilbertBasis H).repr hP]
  exact ⟨hilbert_first_moment (chosenHilbertBasis H).repr hP hψ,
    hilbert_second_moment (chosenHilbertBasis H).repr hP hψ⟩

private lemma moment_bound_of_spectral_moments
    {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
    {S : C →L[ℂ] C} (hpos : 0 ≤ S) (hnorm : ‖S‖ ≤ 1) {α : ℝ}
    (hspec : spectrum ℂ S ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {Ψ : C} {p q : ℝ} (hunit : ⟪Ψ, Ψ⟫_ℂ = 1) (h₁ : ⟪Ψ, S Ψ⟫_ℂ = (p : ℂ))
    (h₂ : ⟪Ψ, S (S Ψ)⟫_ℂ = (((p + 2 * q) / 3 : ℝ) : ℂ)) :
    p - 3 / 2 * α * (1 - p) ≤ q := by
  have hpoly := (spectrum_gap_iff_quadraticForm_nonneg hpos hnorm α).mp hspec Ψ
  rw [h₂, h₁, hunit, mul_one] at hpoly
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, mul_zero, sub_zero] at hpoly
  nlinarith

/-- The moment bound in the proof of Lemma 3.3, using the literal complex spectrum. -/
theorem lojasiewiczData_of_threeCopy_spectrum (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1}) :
    (hilbertTensorSquare H).LojasiewiczData P α := by
  let e := (chosenHilbertBasis H).repr
  rw [threeCopyAverage_eq e hP] at hspec
  intro ψ hψ
  let Ψ := hilbertTmul ψ (hilbertTmul ψ ψ)
  have hunit : ⟪Ψ, Ψ⟫_ℂ = 1 := by
    dsimp only [Ψ]
    rw [inner_hilbertTmul, inner_hilbertTmul, inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  exact moment_bound_of_spectral_moments (S := hilbertAverage e hP) (Ψ := Ψ)
    (p := (hilbertTensorSquare H).accProbA P ψ) (q := (hilbertTensorSquare H).qProbA P ψ)
    (hilbertAverage_nonneg e hP) (hilbertAverage_norm_le_one e hP) hspec hunit
    (hilbert_first_moment e hP hψ) (hilbert_second_moment e hP hψ)

/-- Lemma 3.3. The spectral inclusion gives the manuscript's squared-gradient lower bound. -/
theorem norm_gradAcc_sq_ge_of_threeCopy_spectrum (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (_hα : α ∈ Set.Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    16 * ((hilbertTensorSquare H).accProbA P ψ - 3 / 2 * α) *
      (1 - (hilbertTensorSquare H).accProbA P ψ) ≤ ‖(hilbertTensorSquare H).gradAccA P ψ‖ ^ 2 := by
  rw [(hilbertTensorSquare H).norm_gradAccA_sq hP hψ]
  have hq := lojasiewiczData_of_threeCopy_spectrum hP hspec ψ hψ
  nlinarith

end
end GaussianTesting
