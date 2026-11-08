module

public import GaussianTesting.GradientFlow.HilbertTensor
public import GaussianTesting.GradientFlow.Spectral
public import GaussianTesting.Bosons.ThreeCopy

@[expose] public section

/-!
# Pair operators on the completed Hilbert tensor cube

Tensoring a bounded two-copy operator with the identity gives the three pair
operators of Eq. (3.6), using the unitary swap and reassociation to select the
two factors. Matrix elements on elementary tensors identify these operators
with the coordinate slice operators used to compute the moments.
-/

namespace GaussianTesting

open scoped InnerProductSpace
noncomputable section

private lemma tsum_inner_spectator {ι : Type*} (x y : L2 ι) (u v : L2 (ι × ι)) :
    (∑' i, ⟪x i • u, y i • v⟫_ℂ) = ⟪x, y⟫_ℂ * ⟪u, v⟫_ℂ := by
  simp only [inner_smul_left, inner_smul_right]
  simp_rw [← mul_assoc]
  rw [tsum_mul_right]
  simp only [lp.inner_eq_tsum, RCLike.inner_apply]

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (e : H ≃ₗᵢ[ℂ] L2 ι) {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- A bounded two-copy operator in the Hilbert coordinates determined by `e`. -/
def hilbertPairOpCoords (P : HilbertSquare H →L[ℂ] HilbertSquare H) :=
  (hilbertCoords e e).conjStarAlgEquiv P

lemma hilbertPairOpCoords_apply (P : HilbertSquare H →L[ℂ] HilbertSquare H) (x : HilbertSquare H) :
    hilbertPairOpCoords e P (hilbertCoords e e x) = hilbertCoords e e (P x) := by
  simp [hilbertPairOpCoords]

/-- Conjugation preserves symmetry, idempotence, and commutation with the tensor swap. -/
theorem hilbertPairOpCoords_isAcceptance (hP : (hilbertTensorSquare H).IsAcceptance P) :
    (lpTensorSquare ι).IsAcceptance (hilbertPairOpCoords e P) := by
  let U := hilbertCoords e e
  constructor
  · intro u v
    obtain ⟨x, rfl⟩ := U.surjective u
    obtain ⟨y, rfl⟩ := U.surjective v
    dsimp only [U]
    rw [hilbertPairOpCoords_apply, hilbertPairOpCoords_apply, LinearIsometryEquiv.inner_map_map,
      LinearIsometryEquiv.inner_map_map, hP.symmetric]
  · change hilbertPairOpCoords e P * hilbertPairOpCoords e P = hilbertPairOpCoords e P
    exact (map_mul U.conjStarAlgEquiv P P).symm.trans (congrArg U.conjStarAlgEquiv hP.idem)
  · intro u
    obtain ⟨x, rfl⟩ := U.surjective u
    dsimp only [U]
    rw [← hilbertCoords_swap, hilbertPairOpCoords_apply, hilbertPairOpCoords_apply,
      hP.swap_comm, hilbertCoords_swap]

/-- Coordinates of an elementary cube factor into the three Hilbert coordinates. -/
lemma hilbertCube_coords_tmul (x y z : H) :
    hilbertCoords e (hilbertCoords e e) (hilbertTmul x (hilbertTmul y z)) =
      tp3lp (e x) (e y) (e z) := by
  rw [hilbertCoords_tmul, hilbertCoords_tmul]
  apply lp.ext
  funext p
  simp only [tpPair_apply, tp3lp_apply, mul_assoc]

/-- Apply a bounded two-copy operator to factors 1 and 2, leaving factor 3 fixed. -/
def threeCopyPair12 (P : HilbertSquare H →L[ℂ] HilbertSquare H) :
    HilbertCube H →L[ℂ] HilbertCube H :=
  hilbertAssoc.conjStarAlgEquiv (hilbertTensorMap P (ContinuousLinearMap.id ℂ H))

/-- Apply a bounded two-copy operator to factors 2 and 3, leaving factor 1 fixed. -/
def threeCopyPair23 (P : HilbertSquare H →L[ℂ] HilbertSquare H) :
    HilbertCube H →L[ℂ] HilbertCube H :=
  hilbertTensorMap (ContinuousLinearMap.id ℂ H) P

/-- The cyclic permutation sends `x ⊗ (y ⊗ z)` to `y ⊗ (z ⊗ x)`. -/
def cycleCopies : HilbertCube H ≃ₗᵢ[ℂ] HilbertCube H :=
  hilbertSwap.trans hilbertAssoc

private lemma cycleCopies_tmul (x y z : H) :
    cycleCopies (hilbertTmul x (hilbertTmul y z)) = hilbertTmul y (hilbertTmul z x) := by
  simp [cycleCopies]

/-- Apply a bounded two-copy operator to factors 1 and 3 in that order.
The cyclic permutation puts the spectator first and leaves the pair in
order 3,1, so the square swap restores the order 1,3 for the action of `P`. -/
def threeCopyPair13 (P : HilbertSquare H →L[ℂ] HilbertSquare H) :
    HilbertCube H →L[ℂ] HilbertCube H :=
  cycleCopies.symm.conjStarAlgEquiv (threeCopyPair23 (hilbertSwap.conjStarAlgEquiv P))

/-- Elementary matrix elements of `P ⊗ I` on the reassociated cube. -/
theorem inner_threeCopyPair12_tmul (P : HilbertSquare H →L[ℂ] HilbertSquare H)
    (a b c x y z : H) :
    ⟪hilbertTmul a (hilbertTmul b c), threeCopyPair12 P (hilbertTmul x (hilbertTmul y z))⟫_ℂ =
      ⟪c, z⟫_ℂ * ⟪hilbertTmul a b, P (hilbertTmul x y)⟫_ℂ := by
  rw [← hilbertAssoc_tmul a b c, ← hilbertAssoc_tmul x y z]
  simp only [threeCopyPair12, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, hilbertTensorMap_tmul, ContinuousLinearMap.id_apply,
    LinearIsometryEquiv.inner_map_map, inner_hilbertTmul, mul_comm]

/-- Elementary matrix elements of `I ⊗ P`. The two-copy vectors may be entangled. -/
theorem inner_threeCopyPair23_tmul (P : HilbertSquare H →L[ℂ] HilbertSquare H)
    (a x : H) (b y : HilbertSquare H) :
    ⟪hilbertTmul a b, threeCopyPair23 P (hilbertTmul x y)⟫_ℂ = ⟪a, x⟫_ℂ * ⟪b, P y⟫_ℂ := by
  simp [threeCopyPair23]

/-- Elementary matrix elements for the 1,3 pair factor across the second copy. -/
theorem inner_threeCopyPair13_tmul (P : HilbertSquare H →L[ℂ] HilbertSquare H)
    (a b c x y z : H) :
    ⟪hilbertTmul a (hilbertTmul b c), threeCopyPair13 P (hilbertTmul x (hilbertTmul y z))⟫_ℂ =
      ⟪b, y⟫_ℂ * ⟪hilbertTmul a c, P (hilbertTmul x z)⟫_ℂ := by
  rw [← cycleCopies.inner_map_map]
  simp only [threeCopyPair13, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    cycleCopies_tmul, inner_threeCopyPair23_tmul]
  congr 1
  rw [← hilbertSwap_tmul a c, ← hilbertSwap_tmul x z,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]

variable (hP : (hilbertTensorSquare H).IsAcceptance P)

/-- Apply the two-copy projection to factors 1 and 2. -/
def hilbertPair12 : HilbertCube H →L[ℂ] HilbertCube H :=
  (hilbertCoords e (hilbertCoords e e)).symm.conjStarAlgEquiv
    (q12 (hilbertPairOpCoords e P) (hilbertPairOpCoords_isAcceptance e hP).norm_le_one)

/-- Apply the two-copy projection to factors 1 and 3. -/
def hilbertPair13 : HilbertCube H →L[ℂ] HilbertCube H :=
  (hilbertCoords e (hilbertCoords e e)).symm.conjStarAlgEquiv
    (q13 (hilbertPairOpCoords e P) (hilbertPairOpCoords_isAcceptance e hP).norm_le_one)

/-- Apply the two-copy projection to factors 2 and 3. -/
def hilbertPair23 : HilbertCube H →L[ℂ] HilbertCube H :=
  (hilbertCoords e (hilbertCoords e e)).symm.conjStarAlgEquiv
    (q23 (hilbertPairOpCoords e P) (hilbertPairOpCoords_isAcceptance e hP).norm_le_one)

/-- The average of the three pairwise projections in Eq. (3.6). -/
def hilbertAverage : HilbertCube H →L[ℂ] HilbertCube H :=
  (hilbertCoords e (hilbertCoords e e)).symm.conjStarAlgEquiv
    (Slp (hilbertPairOpCoords_isAcceptance e hP).norm_le_one)

theorem hilbertAverage_eq_sum :
    hilbertAverage e hP = (3 : ℂ)⁻¹ •
      (hilbertPair12 e hP + hilbertPair13 e hP + hilbertPair23 e hP) := by
  simp only [hilbertAverage, Slp, map_smul, map_add, hilbertPair12, hilbertPair13, hilbertPair23]

lemma hilbertAverage_coords (v : HilbertCube H) :
    hilbertCoords e (hilbertCoords e e) (hilbertAverage e hP v) =
      Slp (hilbertPairOpCoords_isAcceptance e hP).norm_le_one (hilbertCoords e (hilbertCoords e e) v) := by
  simp [hilbertAverage]

theorem hilbertAverage_nonneg : 0 ≤ hilbertAverage e hP := by
  exact map_nonneg (hilbertCoords e (hilbertCoords e e)).symm.conjStarAlgEquiv
    (Slp_nonneg _ (hilbertPairOpCoords_isAcceptance e hP))

theorem hilbertAverage_norm_le_one : ‖hilbertAverage e hP‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [hilbertAverage, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.symm_symm]
  simpa only [LinearIsometryEquiv.norm_map, one_mul] using
    (Slp (hilbertPairOpCoords_isAcceptance e hP).norm_le_one).le_of_opNorm_le
      (Slp_norm_le_one _) (hilbertCoords e (hilbertCoords e e) x)

/-- The Hilbert coordinates of an elementary square agree with the coordinate tensor square. -/
lemma hilbertCoords_pair_tmul (x y : H) :
    hilbertCoords e e (hilbertTmul x y) = (lpTensorSquare ι).tp (e x) (e y) := by
  rw [hilbertCoords_tmul]
  with_unfolding_all rfl

private lemma inner_coords_pair (a b x y : H) :
    ⟪(lpTensorSquare ι).tp (e a) (e b),
      hilbertPairOpCoords e P ((lpTensorSquare ι).tp (e x) (e y))⟫_ℂ =
      ⟪hilbertTmul a b, P (hilbertTmul x y)⟫_ℂ := by
  rw [← hilbertCoords_pair_tmul, ← hilbertCoords_pair_tmul, hilbertPairOpCoords_apply,
    LinearIsometryEquiv.inner_map_map]

/-- Matrix elements of the 1,2 pair operator factor across the third copy. -/
theorem inner_hilbertPair12_tmul (a b c x y z : H) :
    ⟪hilbertTmul a (hilbertTmul b c), hilbertPair12 e hP (hilbertTmul x (hilbertTmul y z))⟫_ℂ =
      ⟪c, z⟫_ℂ * ⟪hilbertTmul a b, P (hilbertTmul x y)⟫_ℂ := by
  rw [← (hilbertCoords e (hilbertCoords e e)).inner_map_map]
  simp only [hilbertPair12, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply, hilbertCube_coords_tmul]
  rw [inner_eq_tsum_sl3]
  simp_rw [sl3_q12, sl3_tp3lp, map_smul]
  rw [tsum_inner_spectator, e.inner_map_map, inner_coords_pair]

/-- Matrix elements of the 1,3 pair operator factor across the second copy. -/
theorem inner_hilbertPair13_tmul (a b c x y z : H) :
    ⟪hilbertTmul a (hilbertTmul b c), hilbertPair13 e hP (hilbertTmul x (hilbertTmul y z))⟫_ℂ =
      ⟪b, y⟫_ℂ * ⟪hilbertTmul a c, P (hilbertTmul x z)⟫_ℂ := by
  rw [← (hilbertCoords e (hilbertCoords e e)).inner_map_map]
  simp only [hilbertPair13, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply, hilbertCube_coords_tmul]
  rw [inner_eq_tsum_sl2]
  simp_rw [sl2_q13, sl2_tp3lp, map_smul]
  rw [tsum_inner_spectator, e.inner_map_map, inner_coords_pair]

/-- Matrix elements of the 2,3 pair operator factor across the first copy. -/
theorem inner_hilbertPair23_tmul (a b c x y z : H) :
    ⟪hilbertTmul a (hilbertTmul b c), hilbertPair23 e hP (hilbertTmul x (hilbertTmul y z))⟫_ℂ =
      ⟪a, x⟫_ℂ * ⟪hilbertTmul b c, P (hilbertTmul y z)⟫_ℂ := by
  rw [← (hilbertCoords e (hilbertCoords e e)).inner_map_map]
  simp only [hilbertPair23, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply, hilbertCube_coords_tmul]
  rw [inner_eq_tsum_sl1]
  simp_rw [sl1_q23, sl1_tp3lp, map_smul]
  rw [tsum_inner_spectator, e.inner_map_map, inner_coords_pair]

/-- Matrix elements between elementary cubes uniquely determine a bounded operator. -/
theorem hilbertCube_operator_ext {A B : HilbertCube H →L[ℂ] HilbertCube H}
    (h : ∀ a b c x y z : H, ⟪hilbertTmul a (hilbertTmul b c), A (hilbertTmul x (hilbertTmul y z))⟫_ℂ =
      ⟪hilbertTmul a (hilbertTmul b c), B (hilbertTmul x (hilbertTmul y z))⟫_ℂ) : A = B := by
  apply ContinuousLinearMap.ext_on dense_span_hilbertTriple
  rintro _ ⟨⟨x, y, z⟩, rfl⟩
  apply (InnerProductSpace.toDual ℂ (HilbertCube H)).injective
  apply ContinuousLinearMap.ext_on dense_span_hilbertTriple
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  simpa only [InnerProductSpace.toDual_apply_apply, inner_conj_symm] using
    congrArg (starRingEnd ℂ) (h a b c x y z)

theorem hilbertPair12_eq_threeCopyPair12 : hilbertPair12 e hP = threeCopyPair12 P := by
  apply hilbertCube_operator_ext
  intro a b c x y z
  rw [inner_hilbertPair12_tmul, inner_threeCopyPair12_tmul]

theorem hilbertPair13_eq_threeCopyPair13 : hilbertPair13 e hP = threeCopyPair13 P := by
  apply hilbertCube_operator_ext
  intro a b c x y z
  rw [inner_hilbertPair13_tmul, inner_threeCopyPair13_tmul]

theorem hilbertPair23_eq_threeCopyPair23 : hilbertPair23 e hP = threeCopyPair23 P := by
  apply hilbertCube_operator_ext
  intro a b c x y z
  rw [inner_hilbertPair23_tmul, inner_threeCopyPair23_tmul]

/-- The coordinate slice average equals the average of the three tensor-factor actions
on the completed Hilbert cube. -/
theorem hilbertAverage_eq_threeCopyPairs :
    hilbertAverage e hP = (3 : ℂ)⁻¹ •
      (threeCopyPair12 P + threeCopyPair13 P + threeCopyPair23 P) := by
  rw [hilbertAverage_eq_sum, hilbertPair12_eq_threeCopyPair12, hilbertPair13_eq_threeCopyPair13,
    hilbertPair23_eq_threeCopyPair23]

/-- The average on the completed tensor cube is independent of the Hilbert coordinates
used to construct its pair operators. -/
theorem hilbertAverage_eq_of_coords {κ : Type*} (f : H ≃ₗᵢ[ℂ] L2 κ) :
    hilbertAverage e hP = hilbertAverage f hP := by
  apply hilbertCube_operator_ext
  intro a b c x y z
  simp only [hilbertAverage_eq_sum, smul_apply, add_apply, inner_smul_right, inner_add_right,
    inner_hilbertPair12_tmul, inner_hilbertPair13_tmul, inner_hilbertPair23_tmul]

end
end GaussianTesting
