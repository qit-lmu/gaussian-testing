module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Rotations of two-copy Schrödinger wavefunctions

The coordinate map and its pullback on actual Lebesgue `L²` functions implement
the wavefunction formula for `U_θ` in the manuscript. In particular, the angle
`π / 2` sends `(x,y)` to `(y,-x)`. The pullbacks form a strongly continuous
group of complex linear isometries.
-/

namespace GaussianTesting

open MeasureTheory
open scoped ENNReal

/-- The positions of two copies of an `m`-mode bosonic system. The first index
selects the copy and the second index selects the mode. -/
abbrev BosonConfig (m : ℕ) := EuclideanSpace ℝ (Fin 2 × Fin m)

/-- The two-copy Schrödinger Hilbert space, with Lebesgue measure. -/
noncomputable abbrev SchrodingerSpace (m : ℕ) :=
  MeasureTheory.Lp ℂ 2 (volume : Measure (BosonConfig m))

/-- The coordinate rotation in the manuscript's formula for `U_θ`. -/
noncomputable def bosonRotate {m : ℕ} (θ : ℝ) (z : BosonConfig m) : BosonConfig m :=
  WithLp.toLp 2 fun p => if p.1 = 0 then
    Real.cos θ * z (0, p.2) + Real.sin θ * z (1, p.2)
  else -Real.sin θ * z (0, p.2) + Real.cos θ * z (1, p.2)

@[simp] theorem bosonRotate_zero_apply {m : ℕ} (θ : ℝ) (z : BosonConfig m) (j : Fin m) :
    bosonRotate θ z (0, j) = Real.cos θ * z (0, j) + Real.sin θ * z (1, j) := by
  simp [bosonRotate]

@[simp] theorem bosonRotate_one_apply {m : ℕ} (θ : ℝ) (z : BosonConfig m) (j : Fin m) :
    bosonRotate θ z (1, j) = -Real.sin θ * z (0, j) + Real.cos θ * z (1, j) := by
  simp [bosonRotate]

@[simp] theorem bosonRotate_zero {m : ℕ} (z : BosonConfig m) : bosonRotate 0 z = z := by
  ext ⟨i, j⟩
  fin_cases i <;> simp

theorem bosonRotate_add {m : ℕ} (s t : ℝ) (z : BosonConfig m) :
    bosonRotate (s + t) z = bosonRotate s (bosonRotate t z) := by
  ext ⟨i, j⟩
  fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring

@[simp] theorem bosonRotate_neg_left {m : ℕ} (θ : ℝ) (z : BosonConfig m) :
    bosonRotate (-θ) (bosonRotate θ z) = z := by
  rw [← bosonRotate_add, neg_add_cancel, bosonRotate_zero]

@[simp] theorem bosonRotate_neg_right {m : ℕ} (θ : ℝ) (z : BosonConfig m) :
    bosonRotate θ (bosonRotate (-θ) z) = z := by
  rw [← bosonRotate_add, add_neg_cancel, bosonRotate_zero]

/-- Rotation preserves the Euclidean norm of the position coordinates. -/
theorem norm_bosonRotate {m : ℕ} (θ : ℝ) (z : BosonConfig m) :
    ‖bosonRotate θ z‖ = ‖z‖ := by
  have hsq : ‖bosonRotate θ z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change (Real.cos θ * z (0, j) + Real.sin θ * z (1, j)) ^ 2 +
      (-Real.sin θ * z (0, j) + Real.cos θ * z (1, j)) ^ 2 = _
    nlinarith [congrArg (fun a : ℝ => a * (z (0, j) ^ 2 + z (1, j) ^ 2))
      (Real.sin_sq_add_cos_sq θ)]
  nlinarith [norm_nonneg (bosonRotate θ z), norm_nonneg z]

/-- The coordinate rotation as a linear map, used to construct its isometric equivalence. -/
noncomputable def bosonRotationLinearMap (m : ℕ) (θ : ℝ) :
    BosonConfig m →ₗ[ℝ] BosonConfig m where
  toFun := bosonRotate θ
  map_add' x y := by
    ext ⟨i, j⟩
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext ⟨i, j⟩
    fin_cases i <;> simp <;> ring

/-- The coordinate rotation as an orthogonal linear equivalence. -/
noncomputable def bosonRotation (m : ℕ) (θ : ℝ) :
    BosonConfig m ≃ₗᵢ[ℝ] BosonConfig m :=
  LinearIsometryEquiv.ofLinearIsometry
    { bosonRotationLinearMap m θ with norm_map' := norm_bosonRotate θ }
    (bosonRotationLinearMap m (-θ))
    (by ext z : 1; exact bosonRotate_neg_right θ z)
    (by ext z : 1; exact bosonRotate_neg_left θ z)

@[simp] theorem bosonRotation_apply (m : ℕ) (θ : ℝ) (z : BosonConfig m) :
    bosonRotation m θ z = bosonRotate θ z := rfl

/-- Lebesgue measure is invariant under the two-copy rotations. -/
theorem bosonRotation_measurePreserving (m : ℕ) (θ : ℝ) :
    MeasurePreserving (bosonRotate θ : BosonConfig m → BosonConfig m) :=
  (bosonRotation m θ).measurePreserving

/-- Coordinate rotation is jointly continuous in the angle and the position. -/
theorem continuous_bosonRotate (m : ℕ) :
    Continuous (fun p : ℝ × BosonConfig m => bosonRotate p.1 p.2) := by
  unfold bosonRotate
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 × Fin m => ℝ)).comp
  apply continuous_pi
  rintro ⟨i, j⟩
  fin_cases i <;> simp <;> fun_prop

private noncomputable def bosonRotationContinuousMap (m : ℕ) (θ : ℝ) :
    C(BosonConfig m, BosonConfig m) :=
  ⟨bosonRotate θ, (bosonRotation m θ).continuous⟩

private theorem continuous_bosonRotationContinuousMap (m : ℕ) :
    Continuous (bosonRotationContinuousMap m) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_bosonRotate m)

private theorem rotation_pullback_add (m : ℕ) (s t : ℝ) (f : SchrodingerSpace m) :
    Lp.compMeasurePreserving (bosonRotate s) (bosonRotation_measurePreserving m s)
      (Lp.compMeasurePreserving (bosonRotate t) (bosonRotation_measurePreserving m t) f) =
    Lp.compMeasurePreserving (bosonRotate (s + t))
      (bosonRotation_measurePreserving m (s + t)) f := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (bosonRotate t : BosonConfig m → BosonConfig m) ∘ bosonRotate s =
      bosonRotate (s + t) := by
    funext z
    rw [Function.comp_apply, ← bosonRotate_add, add_comm]
  simp only [h]

private theorem rotation_pullback_zero (m : ℕ) (f : SchrodingerSpace m) :
    Lp.compMeasurePreserving (bosonRotate 0) (bosonRotation_measurePreserving m 0) f = f := by
  have h : (bosonRotate 0 : BosonConfig m → BosonConfig m) = id :=
    funext bosonRotate_zero
  simp [h]

/-- The manuscript's `U_θ`: pullback by the rotation of the two positions. -/
noncomputable def schrodingerRotation (m : ℕ) (θ : ℝ) :
    SchrodingerSpace m ≃ₗᵢ[ℂ] SchrodingerSpace m :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ (bosonRotate θ) (bosonRotation_measurePreserving m θ))
    (Lp.compMeasurePreservingₗ ℂ (bosonRotate (-θ))
      (bosonRotation_measurePreserving m (-θ)))
    (by
      ext f : 1
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [rotation_pullback_add, add_neg_cancel, rotation_pullback_zero])
    (by
      ext f : 1
      change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
      rw [rotation_pullback_add, neg_add_cancel, rotation_pullback_zero])

/-- The pullback formula holds for Lebesgue-almost every position. -/
theorem schrodingerRotation_coeFn (m : ℕ) (θ : ℝ) (f : SchrodingerSpace m) :
    (schrodingerRotation m θ f : BosonConfig m → ℂ) =ᵐ[volume]
      fun z => f (bosonRotate θ z) :=
  Lp.coeFn_compMeasurePreserving f (bosonRotation_measurePreserving m θ)

/-- Pullback of a chosen square-integrable representative. -/
theorem schrodingerRotation_toLp (m : ℕ) (θ : ℝ) {f : BosonConfig m → ℂ}
    (hf : MemLp f 2 volume) :
    schrodingerRotation m θ (hf.toLp f) =
      (hf.comp_measurePreserving (bosonRotation_measurePreserving m θ)).toLp
        (f ∘ bosonRotate θ) := rfl

@[simp] theorem schrodingerRotation_zero (m : ℕ) (f : SchrodingerSpace m) :
    schrodingerRotation m 0 f = f := rotation_pullback_zero m f

/-- The angle-addition law for the unitary group. -/
theorem schrodingerRotation_add (m : ℕ) (s t : ℝ) (f : SchrodingerSpace m) :
    schrodingerRotation m (s + t) f =
      schrodingerRotation m s (schrodingerRotation m t f) :=
  (rotation_pullback_add m s t f).symm

@[simp] theorem schrodingerRotation_neg_left (m : ℕ) (θ : ℝ)
    (f : SchrodingerSpace m) :
    schrodingerRotation m (-θ) (schrodingerRotation m θ f) = f := by
  rw [← schrodingerRotation_add, neg_add_cancel, schrodingerRotation_zero]

@[simp] theorem schrodingerRotation_neg_right (m : ℕ) (θ : ℝ)
    (f : SchrodingerSpace m) :
    schrodingerRotation m θ (schrodingerRotation m (-θ) f) = f := by
  rw [← schrodingerRotation_add, add_neg_cancel, schrodingerRotation_zero]

/-- Strong continuity of the rotation group on the physical Hilbert space. -/
theorem continuous_schrodingerRotation (m : ℕ) (f : SchrodingerSpace m) :
    Continuous (fun θ => schrodingerRotation m θ f) := by
  exact continuous_const.compMeasurePreservingLp
    (continuous_bosonRotationContinuousMap m) (bosonRotation_measurePreserving m) (by norm_num)

/-- Joint continuity also allows both the angle and the wavefunction to vary. -/
theorem continuous_schrodingerRotation_apply (m : ℕ) :
    Continuous (fun p : ℝ × SchrodingerSpace m => schrodingerRotation m p.1 p.2) := by
  exact continuous_snd.compMeasurePreservingLp
    ((continuous_bosonRotationContinuousMap m).comp continuous_fst)
    (fun p => bosonRotation_measurePreserving m p.1) (by norm_num)

/-- The quarter-turn sends the first position to the second. -/
@[simp] theorem bosonRotate_pi_div_two_zero {m : ℕ} (z : BosonConfig m) (j : Fin m) :
    bosonRotate (Real.pi / 2) z (0, j) = z (1, j) := by simp

/-- The quarter-turn sends the second position to the negative of the first. -/
@[simp] theorem bosonRotate_pi_div_two_one {m : ℕ} (z : BosonConfig m) (j : Fin m) :
    bosonRotate (Real.pi / 2) z (1, j) = -z (0, j) := by simp

/-- The signed swap of the two position coordinates. -/
noncomputable def bosonSignedSwap {m : ℕ} (z : BosonConfig m) : BosonConfig m :=
  WithLp.toLp 2 fun p => if p.1 = 0 then z (1, p.2) else -z (0, p.2)

theorem bosonRotate_pi_div_two {m : ℕ} (z : BosonConfig m) :
    bosonRotate (Real.pi / 2) z = bosonSignedSwap z := by
  ext ⟨i, j⟩
  fin_cases i <;> simp [bosonSignedSwap]

/-- The quarter-turn is the signed swap on actual wavefunctions, as used in
the proof of Lemma 6.2. -/
theorem schrodingerRotation_pi_div_two_coeFn (m : ℕ) (f : SchrodingerSpace m) :
    (schrodingerRotation m (Real.pi / 2) f : BosonConfig m → ℂ) =ᵐ[volume]
      fun z => f (bosonSignedSwap z) := by
  simpa only [bosonRotate_pi_div_two] using
    schrodingerRotation_coeFn m (Real.pi / 2) f

end GaussianTesting
