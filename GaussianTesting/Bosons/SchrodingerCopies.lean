module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerRotation
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# Orthogonal actions on many-copy wavefunctions

The copy index is first and the mode index is second. Orthogonal matrices
act on the copy coordinates; inverse pullback defines the manuscript's
unitary representation on actual Lebesgue `L²`. The action is strongly
continuous, and restricts to the special orthogonal group. This construction
does not presume an identification with the Fock coefficient space.
-/

namespace GaussianTesting

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

/-- Position coordinates of `t` copies of an `m`-mode system. -/
abbrev CopiesConfig (m t : ℕ) := EuclideanSpace ℝ (Fin t × Fin m)

/-- The actual Schrödinger space of `t` copies. -/
abbrev CopiesWaveSpace (m t : ℕ) := Lp ℂ 2 (volume : Measure (CopiesConfig m t))

/-- The matrix acts on copies and leaves modes unchanged. -/
def copiesCoordinateMap {m t : ℕ} (A : Matrix (Fin t) (Fin t) ℝ)
    (z : CopiesConfig m t) : CopiesConfig m t :=
  WithLp.toLp 2 fun p => ∑ k, A p.1 k * z (k, p.2)

@[simp] theorem copiesCoordinateMap_apply {m t : ℕ}
    (A : Matrix (Fin t) (Fin t) ℝ) (z : CopiesConfig m t) (i : Fin t) (j : Fin m) :
    copiesCoordinateMap A z (i,j) = ∑ k, A i k * z (k,j) := rfl

@[simp] theorem copiesCoordinateMap_one {m t : ℕ} (z : CopiesConfig m t) :
    copiesCoordinateMap 1 z = z := by
  ext ⟨i,j⟩
  simp [Matrix.one_apply]

theorem copiesCoordinateMap_mul {m t : ℕ}
    (A B : Matrix (Fin t) (Fin t) ℝ) (z : CopiesConfig m t) :
    copiesCoordinateMap (A*B) z = copiesCoordinateMap A (copiesCoordinateMap B z) := by
  ext ⟨i,j⟩
  simp only [copiesCoordinateMap_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem orthogonal_sum_sq {t : ℕ} (O : Matrix.orthogonalGroup (Fin t) ℝ)
    (v : Fin t → ℝ) : ∑ i, (∑ k, O i k * v k)^2 = ∑ i, (v i)^2 := by
  have hO : (O : Matrix (Fin t) (Fin t) ℝ)ᵀ * O = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using O.property.1
  have h : (O.1 *ᵥ v) ⬝ᵥ (O.1 *ᵥ v) = v ⬝ᵥ v := by
    rw [← Matrix.dotProduct_transpose_mulVec O.1 v (O.1 *ᵥ v),
      Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  simpa only [dotProduct, Matrix.mulVec, pow_two] using h

/-- Orthogonal copy transformations preserve the full configuration norm. -/
theorem norm_copiesCoordinateMap {m t : ℕ} (O : Matrix.orthogonalGroup (Fin t) ℝ)
    (z : CopiesConfig m t) : ‖copiesCoordinateMap O z‖ = ‖z‖ := by
  have hs : ‖copiesCoordinateMap O z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
      copiesCoordinateMap_apply]
    calc
      ∑ i, ∑ j, (∑ k, O i k * z (k,j))^2 =
          ∑ j, ∑ i, (∑ k, O i k * z (k,j))^2 := Finset.sum_comm
      _ = ∑ j, ∑ i, z (i,j)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        exact orthogonal_sum_sq O (fun i => z (i,j))
      _ = ∑ i, ∑ j, z (i,j)^2 := Finset.sum_comm
  nlinarith [norm_nonneg (copiesCoordinateMap O z), norm_nonneg z]

/-- Matrix action on the copy coordinate bundled as a linear map. -/
def copiesCoordinateLinear (m t : ℕ) (A : Matrix (Fin t) (Fin t) ℝ) :
    CopiesConfig m t →ₗ[ℝ] CopiesConfig m t where
  toFun := copiesCoordinateMap A
  map_add' x y := by
    ext ⟨i,j⟩
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext ⟨i,j⟩
    simp [Finset.mul_sum, mul_left_comm]

/-- Orthogonal copy action on positions, bundled as a linear isometry. -/
def copiesCoordinateEquiv (m t : ℕ) (O : Matrix.orthogonalGroup (Fin t) ℝ) :
    CopiesConfig m t ≃ₗᵢ[ℝ] CopiesConfig m t :=
  LinearIsometryEquiv.ofLinearIsometry
    { copiesCoordinateLinear m t O with norm_map' := norm_copiesCoordinateMap O }
    (copiesCoordinateLinear m t (O⁻¹ : Matrix.orthogonalGroup (Fin t) ℝ))
    (by
      ext z : 1
      change copiesCoordinateMap O (copiesCoordinateMap (O⁻¹ : Matrix.orthogonalGroup _ _) z) = z
      rw [← copiesCoordinateMap_mul, ← Matrix.UnitaryGroup.mul_val, mul_inv_cancel,
        Matrix.UnitaryGroup.one_val, copiesCoordinateMap_one])
    (by
      ext z : 1
      change copiesCoordinateMap (O⁻¹ : Matrix.orthogonalGroup _ _) (copiesCoordinateMap O z) = z
      rw [← copiesCoordinateMap_mul, ← Matrix.UnitaryGroup.mul_val, inv_mul_cancel,
        Matrix.UnitaryGroup.one_val, copiesCoordinateMap_one])

theorem copiesCoordinateMap_measurePreserving (m t : ℕ)
    (O : Matrix.orthogonalGroup (Fin t) ℝ) :
    MeasurePreserving (copiesCoordinateMap O : CopiesConfig m t → CopiesConfig m t) :=
  (copiesCoordinateEquiv m t O).measurePreserving

private theorem copies_pullback_mul (m t : ℕ)
    (O P : Matrix.orthogonalGroup (Fin t) ℝ) (f : CopiesWaveSpace m t) :
    Lp.compMeasurePreserving (copiesCoordinateMap O)
        (copiesCoordinateMap_measurePreserving m t O)
      (Lp.compMeasurePreserving (copiesCoordinateMap P)
        (copiesCoordinateMap_measurePreserving m t P) f) =
    Lp.compMeasurePreserving (copiesCoordinateMap (P*O))
      (copiesCoordinateMap_measurePreserving m t (P*O)) f := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (copiesCoordinateMap P : CopiesConfig m t → CopiesConfig m t) ∘
      copiesCoordinateMap O = copiesCoordinateMap (P*O) := by
    funext z
    exact (copiesCoordinateMap_mul P O z).symm
  simp only [h]

private theorem copies_pullback_one (m t : ℕ) (f : CopiesWaveSpace m t) :
    Lp.compMeasurePreserving (copiesCoordinateMap (1 : Matrix.orthogonalGroup (Fin t) ℝ))
      (copiesCoordinateMap_measurePreserving m t 1) f = f := by
  have h : (copiesCoordinateMap (1 : Matrix (Fin t) (Fin t) ℝ) :
      CopiesConfig m t → CopiesConfig m t) = id := funext copiesCoordinateMap_one
  simp [h]

/-- The manuscript's orthogonal representation: inverse pullback on positions. -/
def schrodingerCopiesAction (m t : ℕ) (O : Matrix.orthogonalGroup (Fin t) ℝ) :
    CopiesWaveSpace m t ≃ₗᵢ[ℂ] CopiesWaveSpace m t :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ (copiesCoordinateMap (O⁻¹ : Matrix.orthogonalGroup (Fin t) ℝ))
      (copiesCoordinateMap_measurePreserving m t O⁻¹))
    (Lp.compMeasurePreservingₗ ℂ (copiesCoordinateMap O)
      (copiesCoordinateMap_measurePreserving m t O))
    (by
      ext f : 1
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [copies_pullback_mul, mul_inv_cancel, copies_pullback_one])
    (by
      ext f : 1
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [copies_pullback_mul, inv_mul_cancel, copies_pullback_one])

/-- The representation has the prescribed almost-everywhere wavefunction action. -/
theorem schrodingerCopiesAction_coeFn (m t : ℕ)
    (O : Matrix.orthogonalGroup (Fin t) ℝ) (f : CopiesWaveSpace m t) :
    (schrodingerCopiesAction m t O f : CopiesConfig m t → ℂ) =ᵐ[volume]
      fun z => f (copiesCoordinateMap (O⁻¹ : Matrix.orthogonalGroup (Fin t) ℝ) z) :=
  Lp.coeFn_compMeasurePreserving f (copiesCoordinateMap_measurePreserving m t O⁻¹)

@[simp] theorem schrodingerCopiesAction_one (m t : ℕ) (f : CopiesWaveSpace m t) :
    schrodingerCopiesAction m t 1 f = f := by
  change Lp.compMeasurePreserving _ _ f = f
  simpa only [inv_one] using copies_pullback_one m t f

/-- Matrix multiplication agrees with composition of the wavefunction operators. -/
theorem schrodingerCopiesAction_mul (m t : ℕ)
    (O P : Matrix.orthogonalGroup (Fin t) ℝ) (f : CopiesWaveSpace m t) :
    schrodingerCopiesAction m t (O*P) f =
      schrodingerCopiesAction m t O (schrodingerCopiesAction m t P f) := by
  change Lp.compMeasurePreserving _ _ f =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
  rw [copies_pullback_mul]
  simp only [_root_.mul_inv_rev]

/-- The actual unitary representation of the orthogonal group on copies. -/
def schrodingerCopiesRepresentation (m t : ℕ) :
    Matrix.orthogonalGroup (Fin t) ℝ →*
      (CopiesWaveSpace m t ≃ₗᵢ[ℂ] CopiesWaveSpace m t) where
  toFun := schrodingerCopiesAction m t
  map_one' := by ext f : 1; exact schrodingerCopiesAction_one m t f
  map_mul' O P := by ext f : 1; exact schrodingerCopiesAction_mul m t O P f

/-- Coordinate transformations vary continuously with the matrix and position. -/
theorem continuous_copiesCoordinateMap (m t : ℕ) :
    Continuous (fun p : Matrix.orthogonalGroup (Fin t) ℝ × CopiesConfig m t =>
      copiesCoordinateMap p.1 p.2) := by
  unfold copiesCoordinateMap
  apply (PiLp.continuous_toLp 2 (fun _ : Fin t × Fin m => ℝ)).comp
  apply continuous_pi
  rintro ⟨i,j⟩
  apply continuous_finsetSum
  intro k _
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i k).mul
    ((PiLp.continuous_apply 2 _ (k,j)).comp continuous_snd)

private def copiesInverseContinuousMap (m t : ℕ)
    (O : Matrix.orthogonalGroup (Fin t) ℝ) : C(CopiesConfig m t, CopiesConfig m t) :=
  ⟨copiesCoordinateMap (O⁻¹ : Matrix.orthogonalGroup (Fin t) ℝ),
    (copiesCoordinateEquiv m t O⁻¹).continuous⟩

private theorem continuous_copiesInverseContinuousMap (m t : ℕ) :
    Continuous (copiesInverseContinuousMap m t) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Matrix.orthogonalGroup (Fin t) ℝ × CopiesConfig m t =>
    copiesCoordinateMap (p.1⁻¹ : Matrix.orthogonalGroup (Fin t) ℝ) p.2)
  unfold copiesCoordinateMap
  apply (PiLp.continuous_toLp 2 (fun _ : Fin t × Fin m => ℝ)).comp
  apply continuous_pi
  rintro ⟨i,j⟩
  apply continuous_finsetSum
  intro k _
  simp only [Matrix.UnitaryGroup.inv_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, star_trivial]
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem k i).mul
    ((PiLp.continuous_apply 2 _ (k,j)).comp continuous_snd)

/-- Strong continuity of the many-copy orthogonal representation. -/
theorem continuous_schrodingerCopiesAction (m t : ℕ) (f : CopiesWaveSpace m t) :
    Continuous (fun O => schrodingerCopiesAction m t O f) :=
  continuous_const.compMeasurePreservingLp (continuous_copiesInverseContinuousMap m t)
    (fun O => copiesCoordinateMap_measurePreserving m t O⁻¹) (by norm_num)

/-- Joint continuity in the orthogonal matrix and the input wavefunction. -/
theorem continuous_schrodingerCopiesAction_apply (m t : ℕ) :
    Continuous (fun p : Matrix.orthogonalGroup (Fin t) ℝ × CopiesWaveSpace m t =>
      schrodingerCopiesAction m t p.1 p.2) :=
  continuous_snd.compMeasurePreservingLp
    ((continuous_copiesInverseContinuousMap m t).comp continuous_fst)
    (fun p => copiesCoordinateMap_measurePreserving m t p.1⁻¹) (by norm_num)

/-- Forgetting determinant one includes the special orthogonal copy group. -/
def specialOrthogonalCopiesInclusion (t : ℕ) :
    Matrix.specialOrthogonalGroup (Fin t) ℝ →* Matrix.orthogonalGroup (Fin t) ℝ where
  toFun O := ⟨O.val, O.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_specialOrthogonalCopiesInclusion (t : ℕ) :
    Continuous (specialOrthogonalCopiesInclusion t) :=
  continuous_subtype_val.subtype_mk _

/-- The many-copy `SO(t)` representation used in the manuscript. -/
def schrodingerSpecialOrthogonalRepresentation (m t : ℕ) :
    Matrix.specialOrthogonalGroup (Fin t) ℝ →*
      (CopiesWaveSpace m t ≃ₗᵢ[ℂ] CopiesWaveSpace m t) :=
  (schrodingerCopiesRepresentation m t).comp (specialOrthogonalCopiesInclusion t)

/-- The special orthogonal representation is strongly continuous. -/
theorem continuous_schrodingerSpecialOrthogonalRepresentation (m t : ℕ)
    (f : CopiesWaveSpace m t) :
    Continuous (fun O => schrodingerSpecialOrthogonalRepresentation m t O f) :=
  (continuous_schrodingerCopiesAction m t f).comp
    (continuous_specialOrthogonalCopiesInclusion t)

/-- Joint continuity also holds after restriction to `SO(t)`. -/
theorem continuous_schrodingerSpecialOrthogonalRepresentation_apply (m t : ℕ) :
    Continuous (fun p : Matrix.specialOrthogonalGroup (Fin t) ℝ × CopiesWaveSpace m t =>
      schrodingerSpecialOrthogonalRepresentation m t p.1 p.2) := by
  have h : Continuous (fun p : Matrix.specialOrthogonalGroup (Fin t) ℝ × CopiesWaveSpace m t =>
      (specialOrthogonalCopiesInclusion t p.1, p.2)) :=
    ((continuous_specialOrthogonalCopiesInclusion t).comp continuous_fst).prodMk continuous_snd
  apply ((continuous_schrodingerCopiesAction_apply m t).comp h).congr
  intro p
  rfl

/-- The positive-angle rotation matrix on two copy coordinates. Its inverse
pullback has exactly the manuscript's convention for `U_θ`. -/
def copiesPlaneRotation (θ : ℝ) : Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, rfl, ?_⟩
    simpa only [neg_sq, add_comm] using Real.sin_sq_add_cos_sq θ⟩

/-- The inverse matrix action specializes to the existing two-copy rotation. -/
theorem copiesPlaneRotation_inverse_coordinates (m : ℕ) (θ : ℝ) (z : BosonConfig m) :
    copiesCoordinateMap ((specialOrthogonalCopiesInclusion 2 (copiesPlaneRotation θ))⁻¹ :
      Matrix.orthogonalGroup (Fin 2) ℝ) z = bosonRotate θ z := by
  ext ⟨i,j⟩
  fin_cases i <;>
    simp [copiesCoordinateMap_apply, specialOrthogonalCopiesInclusion, copiesPlaneRotation,
      Matrix.star_eq_conjTranspose, Fin.sum_univ_two]

/-- At two copies the general representation is exactly `schrodingerRotation`. -/
theorem schrodingerSpecialOrthogonalRepresentation_planeRotation (m : ℕ) (θ : ℝ) :
    schrodingerSpecialOrthogonalRepresentation m 2 (copiesPlaneRotation θ) =
      schrodingerRotation m θ := by
  ext f : 1
  apply Lp.ext
  filter_upwards [schrodingerCopiesAction_coeFn m 2
      (specialOrthogonalCopiesInclusion 2 (copiesPlaneRotation θ)) f,
    schrodingerRotation_coeFn m θ f] with z hz hz'
  exact hz.trans ((congrArg (fun z => f z)
    (copiesPlaneRotation_inverse_coordinates m θ z)).trans hz'.symm)

end
end GaussianTesting
