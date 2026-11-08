module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.GradientFlow.HilbertSpectralGap
public import GaussianTesting.GradientFlow.HilbertTensorFour
public import GaussianTesting.GradientFlow.Moments
public import Mathlib.Analysis.Normed.Lp.LpEquiv

@[expose] public section

/-!
# Finite occupation coordinates for the completed-tensor robustness theorem

The finite product-index Hilbert spaces are unitarily identified with the
completed tensor square and cube. This allows finite models to use the
manuscript's projective-flow proof of Theorem 3.4 directly.
-/

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Finite Euclidean coordinates as square-summable coordinates. -/
def finiteL2Equiv (ι : Type*) [Fintype ι] : H ι ≃ₗᵢ[ℂ] L2 ι :=
  (lpPiLpₗᵢ (fun _ : ι => ℂ) ℂ (p := 2)).symm

/-- Product coordinates on the completed tensor product of finite Hilbert spaces. -/
def finiteHilbertTensor (ι κ : Type*) [Fintype ι] [Fintype κ] :
    HilbertTensor (H ι) (H κ) ≃ₗᵢ[ℂ] H (ι × κ) :=
  (hilbertCoords (finiteL2Equiv ι) (finiteL2Equiv κ)).trans (finiteL2Equiv (ι × κ)).symm

@[simp] theorem finiteHilbertTensor_tmul (ψ : H ι) (φ : H κ) :
    finiteHilbertTensor ι κ (hilbertTmul ψ φ) = tp2 ψ φ := by
  simp only [finiteHilbertTensor, LinearIsometryEquiv.trans_apply, hilbertCoords_tmul]
  rfl

abbrev finiteHilbertSquare (ι : Type*) [Fintype ι] :
    HilbertSquare (H ι) ≃ₗᵢ[ℂ] H2 ι := finiteHilbertTensor ι ι

/-- The completed tensor cube in finite product coordinates. -/
def finiteHilbertCube (ι : Type*) [Fintype ι] :
    HilbertCube (H ι) ≃ₗᵢ[ℂ] H3 ι :=
  (hilbertTensorEquiv (LinearIsometryEquiv.refl ℂ (H ι)) (finiteHilbertSquare ι)).trans
    (finiteHilbertTensor ι (ι × ι))

@[simp] theorem finiteHilbertCube_tmul (ψ φ χ : H ι) :
    finiteHilbertCube ι (hilbertTmul ψ (hilbertTmul φ χ)) = tp3 ψ φ χ := by
  simp [finiteHilbertCube, tp3_eq_tp2_tp2]

theorem finiteHilbertSquare_swap (v : HilbertSquare (H ι)) :
    finiteHilbertSquare ι (hilbertSwap v) = swap2 (finiteHilbertSquare ι v) := by
  apply hilbertTensor_induction
    (p := fun w => finiteHilbertSquare ι (hilbertSwap w) = swap2 (finiteHilbertSquare ι w))
    (isClosed_eq ((finiteHilbertSquare ι).continuous.comp hilbertSwap.continuous)
      (swap2.continuous.comp (finiteHilbertSquare ι).continuous)) ?_ ?_ v
  · intro ψ φ
    simp
  · intro u w hu hw
    simp only [map_add, hu, hw]

/-- A finite two-copy operator transported to the completed tensor square. -/
def finiteHilbertProjection (P : H2 ι →ₗ[ℂ] H2 ι) :
    HilbertSquare (H ι) →L[ℂ] HilbertSquare (H ι) :=
  (finiteHilbertSquare ι).symm.conjStarAlgEquiv P.toContinuousLinearMap

@[simp] theorem finiteHilbertProjection_coords (P : H2 ι →ₗ[ℂ] H2 ι)
    (v : HilbertSquare (H ι)) :
    finiteHilbertSquare ι (finiteHilbertProjection P v) = P (finiteHilbertSquare ι v) := by
  simp [finiteHilbertProjection]

theorem finiteHilbertProjection_isAcceptance {P : H2 ι →ₗ[ℂ] H2 ι}
    (hP : IsAcceptanceProjection P) :
    (hilbertTensorSquare (H ι)).IsAcceptance (finiteHilbertProjection P) := by
  constructor
  · intro u v
    rw [← (finiteHilbertSquare ι).inner_map_map u,
      ← (finiteHilbertSquare ι).inner_map_map _ v]
    simp only [finiteHilbertProjection_coords]
    exact hP.symmetric _ _
  · apply ContinuousLinearMap.ext
    intro v
    apply (finiteHilbertSquare ι).injective
    change finiteHilbertSquare ι (finiteHilbertProjection P (finiteHilbertProjection P v)) = _
    simp only [finiteHilbertProjection_coords]
    exact congrArg (fun T : H2 ι →ₗ[ℂ] H2 ι => T (finiteHilbertSquare ι v)) hP.idem
  · intro v
    apply (finiteHilbertSquare ι).injective
    change finiteHilbertSquare ι (finiteHilbertProjection P (hilbertSwap v)) =
      finiteHilbertSquare ι (hilbertSwap (finiteHilbertProjection P v))
    rw [finiteHilbertProjection_coords, finiteHilbertSquare_swap,
      finiteHilbertSquare_swap, finiteHilbertProjection_coords, hP.swap_comm]

@[simp] theorem finiteHilbert_accProb (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) :
    (hilbertTensorSquare (H ι)).accProbA (finiteHilbertProjection P) ψ = accProb P ψ := by
  unfold TensorSquare.accProbA accProb
  change (inner ℂ (hilbertTmul ψ ψ) (finiteHilbertProjection P (hilbertTmul ψ ψ))).re = _
  rw [← (finiteHilbertSquare ι).inner_map_map]
  simp

omit [Fintype ι] in
private theorem finite_slice3_tp3 (k : ι) (a b c : H ι) :
    slice3 k (tp3 a b c) = c k • tp2 a b := by
  ext p
  simp only [slice3_apply, tp3_apply, PiLp.smul_apply, tp2_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
private theorem finite_slice1_tp3 (k : ι) (a b c : H ι) :
    slice1 k (tp3 a b c) = a k • tp2 b c := by
  ext p
  simp only [slice1_apply, tp3_apply, PiLp.smul_apply, tp2_apply, smul_eq_mul]
  ring

omit [Fintype ι] in
private theorem finite_slice2_tp3 (k : ι) (a b c : H ι) :
    slice2 k (tp3 a b c) = b k • tp2 a c := by
  ext p
  simp only [slice2_apply, tp3_apply, PiLp.smul_apply, tp2_apply, smul_eq_mul]
  ring

private theorem finite_inner_p12 (P : H2 ι →ₗ[ℂ] H2 ι) (a b c x y z : H ι) :
    ⟪tp3 a b c, p12 P (tp3 x y z)⟫_ℂ =
      ⟪c, z⟫_ℂ * ⟪tp2 a b, P (tp2 x y)⟫_ℂ := by
  rw [inner_eq_sum_slice3]
  simp only [slice3_p12, finite_slice3_tp3, map_smul, inner_smul_left, inner_smul_right]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul, mul_assoc]

private theorem finite_inner_p23 (P : H2 ι →ₗ[ℂ] H2 ι) (a b c x y z : H ι) :
    ⟪tp3 a b c, p23 P (tp3 x y z)⟫_ℂ =
      ⟪a, x⟫_ℂ * ⟪tp2 b c, P (tp2 y z)⟫_ℂ := by
  rw [inner_eq_sum_slice1]
  simp only [slice1_p23, finite_slice1_tp3, map_smul, inner_smul_left, inner_smul_right]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul, mul_assoc]

private theorem finite_inner_p13 (P : H2 ι →ₗ[ℂ] H2 ι) (a b c x y z : H ι) :
    ⟪tp3 a b c, p13 P (tp3 x y z)⟫_ℂ =
      ⟪b, y⟫_ℂ * ⟪tp2 a c, P (tp2 x z)⟫_ℂ := by
  rw [inner_eq_sum_slice2]
  simp only [slice2_p13, finite_slice2_tp3, map_smul, inner_smul_left, inner_smul_right]
  simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.sum_mul, mul_assoc]

private theorem finite_inner_projected_pair (P : H2 ι →ₗ[ℂ] H2 ι) (a b x y : H ι) :
    ⟪hilbertTmul a b, finiteHilbertProjection P (hilbertTmul x y)⟫_ℂ =
      ⟪tp2 a b, P (tp2 x y)⟫_ℂ := by
  rw [← (finiteHilbertSquare ι).inner_map_map]
  simp

theorem finiteHilbert_pair12 (P : H2 ι →ₗ[ℂ] H2 ι) :
    threeCopyPair12 (finiteHilbertProjection P) =
      (finiteHilbertCube ι).symm.conjStarAlgEquiv (p12 P).toContinuousLinearMap := by
  apply hilbertCube_operator_ext
  intro a b c x y z
  rw [inner_threeCopyPair12_tmul, finite_inner_projected_pair]
  rw [← (finiteHilbertCube ι).inner_map_map]
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply] using (finite_inner_p12 P a b c x y z).symm

theorem finiteHilbert_pair23 (P : H2 ι →ₗ[ℂ] H2 ι) :
    threeCopyPair23 (finiteHilbertProjection P) =
      (finiteHilbertCube ι).symm.conjStarAlgEquiv (p23 P).toContinuousLinearMap := by
  apply hilbertCube_operator_ext
  intro a b c x y z
  rw [inner_threeCopyPair23_tmul, finite_inner_projected_pair]
  rw [← (finiteHilbertCube ι).inner_map_map]
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply] using (finite_inner_p23 P a b c x y z).symm

theorem finiteHilbert_pair13 (P : H2 ι →ₗ[ℂ] H2 ι) :
    threeCopyPair13 (finiteHilbertProjection P) =
      (finiteHilbertCube ι).symm.conjStarAlgEquiv (p13 P).toContinuousLinearMap := by
  apply hilbertCube_operator_ext
  intro a b c x y z
  rw [inner_threeCopyPair13_tmul, finite_inner_projected_pair]
  rw [← (finiteHilbertCube ι).inner_map_map]
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply] using (finite_inner_p13 P a b c x y z).symm

/-- The intrinsic three-copy average is the finite-coordinate average under
the completed-tensor unitary identification. -/
theorem finiteHilbert_average (P : H2 ι →ₗ[ℂ] H2 ι) :
    threeCopyAverage (finiteHilbertProjection P) =
      (finiteHilbertCube ι).symm.conjStarAlgEquiv (Sop P).toContinuousLinearMap := by
  rw [threeCopyAverage, finiteHilbert_pair12, finiteHilbert_pair13, finiteHilbert_pair23,
    ← map_add, ← map_add, ← map_smul]
  congr 1

/-- Spectra agree under the finite-coordinate tensor identification. -/
theorem finiteHilbert_average_spectrum (P : H2 ι →ₗ[ℂ] H2 ι) :
    spectrum ℂ (threeCopyAverage (finiteHilbertProjection P)) =
      spectrum ℂ (Sop P).toContinuousLinearMap := by
  rw [finiteHilbert_average]
  exact AlgEquiv.spectrum_eq (finiteHilbertCube ι).symm.conjStarAlgEquiv _

/-- Finite-coordinate specialization of Theorem 3.4, using the manuscript's
projective gradient-flow proof on the genuine completed tensor products. -/
theorem finite_robustness_of_spectrum {P : H2 ι →ₗ[ℂ] H2 ι}
    (hP : IsAcceptanceProjection P) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (Sop P).toContinuousLinearMap ⊆
      Complex.ofReal '' Set.Icc 0 α ∪ {1})
    (hne : (certaintyStates (accProb P)).Nonempty)
    {ψ : H ι} (hψ : ‖ψ‖ = 1) : RobustnessBounds (accProb P) α ψ := by
  have hp : (hilbertTensorSquare (H ι)).accProbA (finiteHilbertProjection P) = accProb P :=
    funext (finiteHilbert_accProb P)
  rw [← hp] at hne ⊢
  apply robustness_of_threeCopy_spectrum (finiteHilbertProjection_isAcceptance hP)
    hα0 hα ?_ hne hψ
  rwa [finiteHilbert_average_spectrum]

end
end GaussianTesting
