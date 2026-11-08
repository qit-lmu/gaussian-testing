module

public import GaussianTesting.GradientFlow.HilbertPairOperators

@[expose] public section

/-!
# The first two moments on the completed Hilbert tensor cube

Lemma 3.2 is invariant under unitary changes of coordinates. In coordinates,
`inner_tp3lp_Slp` and `inner_Slp_Slp` expand the average of the three pair
projections: the three diagonal terms contribute `p` each, and the six cross
terms contribute the squared norm `q` of the contraction. The Riesz identity
for the contraction transports this last quantity back to the original space.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H ≃ₗᵢ[ℂ] L2 ι) {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- The unitary coordinates preserve the contraction against a tensor factor. -/
theorem hilbert_contr_coords (φ : H) (Y : HilbertSquare H) :
    e ((hilbertTensorSquare H).contr φ Y) =
      (lpTensorSquare ι).contr (e φ) (hilbertCoords e e Y) := by
  apply ext_inner_left ℂ
  intro z
  obtain ⟨v, rfl⟩ := e.surjective z
  rw [e.inner_map_map, TensorSquare.inner_contr, TensorSquare.inner_contr,
    ← hilbertCoords_pair_tmul e, (hilbertCoords e e).inner_map_map]
  rfl

omit [CompleteSpace H] in
private lemma hilbert_accProb_coords (ψ : H) :
    (hilbertTensorSquare H).accProbA P ψ =
      (lpTensorSquare ι).accProbA (hilbertPairOpCoords e P) (e ψ) := by
  unfold TensorSquare.accProbA
  rw [← hilbertCoords_pair_tmul e, hilbertPairOpCoords_apply, (hilbertCoords e e).inner_map_map]
  rfl

private lemma hilbert_qProb_coords (ψ : H) :
    (hilbertTensorSquare H).qProbA P ψ =
      (lpTensorSquare ι).qProbA (hilbertPairOpCoords e P) (e ψ) := by
  unfold TensorSquare.qProbA TensorSquare.KvecA
  rw [← hilbertCoords_pair_tmul e, hilbertPairOpCoords_apply, ← hilbert_contr_coords, e.norm_map]
  rfl

omit [CompleteSpace H] in
/-- Lemma 3.2, first moment: the expectation of the three-pair average on the
elementary cube of a unit vector equals its two-copy acceptance probability. -/
theorem hilbert_first_moment (hP : (hilbertTensorSquare H).IsAcceptance P)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    ⟪hilbertTmul ψ (hilbertTmul ψ ψ),
      hilbertAverage e hP (hilbertTmul ψ (hilbertTmul ψ ψ))⟫_ℂ =
      ((hilbertTensorSquare H).accProbA P ψ : ℂ) := by
  rw [hilbert_accProb_coords e, ← (hilbertCoords e (hilbertCoords e e)).inner_map_map,
    hilbertAverage_coords, hilbertCube_coords_tmul]
  apply inner_tp3lp_Slp _ (hilbertPairOpCoords_isAcceptance e hP)
  simpa only [e.norm_map] using hψ

/-- Lemma 3.2, second moment: the expectation of the square of the three-pair
average gives the combination of the two-copy acceptance and contraction norm. -/
theorem hilbert_second_moment (hP : (hilbertTensorSquare H).IsAcceptance P)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    ⟪hilbertTmul ψ (hilbertTmul ψ ψ),
      hilbertAverage e hP (hilbertAverage e hP (hilbertTmul ψ (hilbertTmul ψ ψ)))⟫_ℂ =
      ((((hilbertTensorSquare H).accProbA P ψ + 2 * (hilbertTensorSquare H).qProbA P ψ) / 3 : ℝ) : ℂ) := by
  have hself := ContinuousLinearMap.nonneg_iff_isPositive.mp (hilbertAverage_nonneg e hP)
  rw [← hself.inner_left_eq_inner_right, hilbert_accProb_coords e, hilbert_qProb_coords e,
    ← (hilbertCoords e (hilbertCoords e e)).inner_map_map, hilbertAverage_coords, hilbertCube_coords_tmul]
  apply inner_Slp_Slp _ (hilbertPairOpCoords_isAcceptance e hP)
  simpa only [e.norm_map] using hψ

end

end GaussianTesting
