module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.WeylRotation
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Unitary linear changes of position coordinates

Invertible real coordinate changes act on the actual Schrödinger space with
Jacobian factor `sqrt |det A|`: `U_A f(x) = sqrt |det A| f(Ax)`.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The positive normalization for pullback by an invertible position map. -/
def linearCoordinateChangeScale (A : E ≃L[ℝ] E) : ℝ :=
  Real.sqrt |LinearMap.det A.toLinearEquiv.toLinearMap|

theorem linearCoordinateChangeScale_pos (A : E ≃L[ℝ] E) :
    0 < linearCoordinateChangeScale A := by
  apply Real.sqrt_pos.mpr
  exact abs_pos.mpr (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero

theorem linearCoordinateChangeScale_symm (A : E ≃L[ℝ] E) :
    linearCoordinateChangeScale A.symm = (linearCoordinateChangeScale A)⁻¹ := by
  unfold linearCoordinateChangeScale
  change Real.sqrt |LinearMap.det A.toLinearEquiv.symm.toLinearMap| = _
  rw [LinearEquiv.det_coe_symm, abs_inv, Real.sqrt_inv]

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

/-- The change-of-variables measure factor. -/
theorem linearCoordinateChange_map_volume (A : E ≃L[ℝ] E) :
    Measure.map A volume =
      ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • volume :=
  map_linearMap_addHaar_eq_smul_addHaar volume
    (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero

theorem linearCoordinateChange_quasiMeasurePreserving 
    (A : E ≃L[ℝ] E) : QuasiMeasurePreserving A volume volume :=
  A.toLinearEquiv.toLinearMap.quasiMeasurePreserving volume
    (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero

private theorem linearChange_memLp (A : E ≃L[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    MemLp (fun x => (linearCoordinateChangeScale A : ℂ) * f (A x)) 2 volume := by
  have hf : MemLp (f : E → ℂ) 2 (Measure.map A volume) := by
    rw [linearCoordinateChange_map_volume]
    exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top
  exact (hf.comp_of_map A.continuous.measurable.aemeasurable).const_mul
    (linearCoordinateChangeScale A : ℂ)

/-- Jacobian-normalized pullback by an invertible linear coordinate map. -/
def linearChangeApply (A : E ≃L[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure E) :=
  ((by exact linearChange_memLp A f) :
    MemLp (fun x => (linearCoordinateChangeScale A : ℂ) * f (A x)) 2 volume).toLp _

private theorem linearChangeApply_coeFn (A : E ≃L[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    (linearChangeApply A f : E → ℂ) =ᵐ[volume]
      fun x => (linearCoordinateChangeScale A : ℂ) * f (A x) := (linearChange_memLp A f).coeFn_toLp

/-- Jacobian-normalized pullback bundled as a complex linear map. -/
def linearChangeLinear (A : E ≃L[ℝ] E) :
    Lp ℂ 2 (volume : Measure E) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) where
  toFun := linearChangeApply A
  map_add' f g := by
    apply Lp.ext
    filter_upwards [linearChangeApply_coeFn A (f+g), linearChangeApply_coeFn A f,
      linearChangeApply_coeFn A g, Lp.coeFn_add (linearChangeApply A f) (linearChangeApply A g),
      (linearCoordinateChange_quasiMeasurePreserving A).ae_eq_comp (Lp.coeFn_add f g)] with x h h₁ h₂ h₃ h₄
    simp only [Function.comp_apply, Pi.add_apply] at h₄
    simp only [h, h₃, h₁, h₂, h₄, Pi.add_apply, mul_add]
  map_smul' c f := by
    change linearChangeApply A (c • f) = c • linearChangeApply A f
    apply Lp.ext
    filter_upwards [linearChangeApply_coeFn A (c • f), linearChangeApply_coeFn A f,
      Lp.coeFn_smul c (linearChangeApply A f),
      (linearCoordinateChange_quasiMeasurePreserving A).ae_eq_comp (Lp.coeFn_smul c f)] with x h h₁ h₂ h₃
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h₃
    simp only [h, h₂, h₁, h₃, Pi.smul_apply, smul_eq_mul, mul_left_comm]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
private theorem configuration_norm_sq_integral (f : Lp ℂ 2 (volume : Measure E)) :
    ‖f‖ ^ 2 = ∫ x : E, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm

private theorem linearChangeApply_norm (A : E ≃L[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) : ‖linearChangeApply A f‖ = ‖f‖ := by
  have hdet : LinearMap.det A.toLinearEquiv.toLinearMap ≠ 0 :=
    (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  have hnorm : ‖linearChangeApply A f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [configuration_norm_sq_integral, configuration_norm_sq_integral]
    calc
      _ = ∫ x : E, linearCoordinateChangeScale A ^ 2 * ‖f (A x)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [linearChangeApply_coeFn A f] with x hx
        rw [hx, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (linearCoordinateChangeScale_pos A)]
      _ = linearCoordinateChangeScale A ^ 2 * ∫ x : E, ‖f (A x)‖ ^ 2 :=
        integral_const_mul _ _
      _ = linearCoordinateChangeScale A ^ 2 *
          ∫ x : E, ‖f x‖ ^ 2 ∂Measure.map A volume := by
        congr 1
        exact (A.toHomeomorph.measurableEmbedding.integral_map
          (μ := volume) (fun x => ‖f x‖ ^ 2)).symm
      _ = ∫ x : E, ‖f x‖ ^ 2 := by
        rw [linearCoordinateChange_map_volume, integral_smul_measure,
          ENNReal.toReal_ofReal (abs_nonneg _)]
        simp only [smul_eq_mul, linearCoordinateChangeScale,
          Real.sq_sqrt (abs_nonneg _), abs_inv]
        rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hdet), one_mul]
  nlinarith [norm_nonneg (linearChangeApply A f), norm_nonneg f]

private theorem linearChangeApply_symm 
    (A : E ≃L[ℝ] E) (f : Lp ℂ 2 (volume : Measure E)) :
    linearChangeApply A (linearChangeApply A.symm f) = f := by
  apply Lp.ext
  filter_upwards [linearChangeApply_coeFn A (linearChangeApply A.symm f),
    (linearCoordinateChange_quasiMeasurePreserving A).ae_eq_comp
      (linearChangeApply_coeFn A.symm f)] with x hx hy
  simp only [Function.comp_apply] at hy
  rw [hx, hy, A.symm_apply_apply, linearCoordinateChangeScale_symm,
    Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (ne_of_gt (linearCoordinateChangeScale_pos A))

/-- Jacobian-normalized pullback is unitary on all Schrödinger wavefunctions. -/
def linearCoordinateChange (A : E ≃L[ℝ] E) :
    Lp ℂ 2 (volume : Measure E) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  LinearIsometryEquiv.ofLinearIsometry
    { linearChangeLinear A with norm_map' := by exact linearChangeApply_norm A }
    (linearChangeLinear A.symm)
    (by ext f : 1; exact linearChangeApply_symm A f)
    (by ext f : 1; exact linearChangeApply_symm A.symm f)

theorem linearCoordinateChange_coeFn (A : E ≃L[ℝ] E)
    (f : Lp ℂ 2 (volume : Measure E)) :
    (linearCoordinateChange A f : E → ℂ) =ᵐ[volume]
      fun x => (linearCoordinateChangeScale A : ℂ) * f (A x) := linearChangeApply_coeFn A f

@[simp] theorem linearCoordinateChange_symm
    (A : E ≃L[ℝ] E) :
    (linearCoordinateChange A).symm = linearCoordinateChange A.symm := by
  ext f : 1
  apply (linearCoordinateChange A).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (linearChangeApply_symm A f).symm


end General

/-- The Jacobian-normalized change of one-copy position coordinates. -/
abbrev waveLinearChange (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m := linearCoordinateChange A

abbrev waveLinearChangeScale {m : ℕ} (A : WaveConfig m ≃L[ℝ] WaveConfig m) : ℝ :=
  linearCoordinateChangeScale A

theorem waveLinearChange_coeFn (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (f : WaveSpace m) :
    (waveLinearChange m A f : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => (waveLinearChangeScale A : ℂ) * f (A x) := linearCoordinateChange_coeFn A f

theorem waveLinearChange_quasiMeasurePreserving {m : ℕ}
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) : QuasiMeasurePreserving A volume volume :=
  linearCoordinateChange_quasiMeasurePreserving A

/-- The inverse symplectic action induced by normalized position pullback. -/
def waveLinearChangePhase {m : ℕ} (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (r : WavePhase m) : WavePhase m :=
  (A r.1, A.symm.toContinuousLinearMap.adjoint r.2)

private theorem weylPhase_linearChange {m : ℕ}
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (r : WavePhase m) (x : WaveConfig m) :
    weylPhase (waveLinearChangePhase A r) (A x) = weylPhase r x := by
  simp only [weylPhase, waveLinearChangePhase,
    ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearEquiv.coe_coe, A.symm_apply_apply]

/-- Coordinate pullback conjugates Weyl displacements by the corresponding
linear symplectic map. -/
theorem waveLinearChange_weyl (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (r : WavePhase m) (f : WaveSpace m) :
    (waveLinearChange m A).symm (weylOperator m r (waveLinearChange m A f)) =
      weylOperator m (waveLinearChangePhase A r) f := by
  apply (waveLinearChange m A).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [weylOperator_coeFn m r (waveLinearChange m A f),
    (waveTranslation_measurePreserving r.1).quasiMeasurePreserving.ae_eq_comp
      (waveLinearChange_coeFn m A f),
    waveLinearChange_coeFn m A (weylOperator m (waveLinearChangePhase A r) f),
    (waveLinearChange_quasiMeasurePreserving A).ae_eq_comp
      (weylOperator_coeFn m (waveLinearChangePhase A r) f)] with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂ h₄
  rw [h₁, h₂, h₃, h₄, weylPhase_linearChange]
  simp only [waveLinearChangePhase, map_sub]
  ring

/-- The induced phase-space map preserves the symplectic form. -/
theorem waveLinearChange_symplectic (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (r s : WavePhase m) :
    waveSymplectic (waveLinearChangePhase A r) (waveLinearChangePhase A s) =
      waveSymplectic r s := by
  simp only [waveSymplectic, waveLinearChangePhase,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe, A.symm_apply_apply]


/-- Split the two-copy position configuration into its two factors. -/
def splitBosonLinearEquiv (m : ℕ) :
    BosonConfig m ≃ₗ[ℝ] WaveConfig m × WaveConfig m :=
  (splitConfigIsometry m).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℝ (WaveConfig m × WaveConfig m))

/-- Apply one invertible position map to each of the two copies. -/
def bosonLinearChange (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    BosonConfig m ≃L[ℝ] BosonConfig m :=
  ((splitBosonLinearEquiv m).trans
    ((A.toLinearEquiv.prodCongr A.toLinearEquiv).trans
      (splitBosonLinearEquiv m).symm)).toContinuousLinearEquiv

@[simp] theorem bosonPosition_linearChange_zero (m : ℕ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (z : BosonConfig m) :
    bosonPosition 0 (bosonLinearChange m A z) = A (bosonPosition 0 z) := by
  ext j
  rfl

@[simp] theorem bosonPosition_linearChange_one (m : ℕ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (z : BosonConfig m) :
    bosonPosition 1 (bosonLinearChange m A z) = A (bosonPosition 1 z) := by
  ext j
  rfl

theorem bosonLinearChange_det (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    LinearMap.det (bosonLinearChange m A).toLinearEquiv.toLinearMap =
      LinearMap.det A.toLinearEquiv.toLinearMap * LinearMap.det A.toLinearEquiv.toLinearMap := by
  change LinearMap.det (((splitBosonLinearEquiv m).symm :
      (WaveConfig m × WaveConfig m) →ₗ[ℝ] BosonConfig m) ∘ₗ
    LinearMap.prodMap A.toLinearEquiv.toLinearMap A.toLinearEquiv.toLinearMap ∘ₗ
      (splitBosonLinearEquiv m : BosonConfig m →ₗ[ℝ] WaveConfig m × WaveConfig m)) = _
  exact (LinearMap.det_conj
    (LinearMap.prodMap A.toLinearEquiv.toLinearMap A.toLinearEquiv.toLinearMap)
    (splitBosonLinearEquiv m).symm).trans (LinearMap.det_prodMap _ _)

theorem bosonLinearChange_scale (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    linearCoordinateChangeScale (bosonLinearChange m A) = waveLinearChangeScale A ^ 2 := by
  unfold waveLinearChangeScale
  simp only [linearCoordinateChangeScale]
  rw [bosonLinearChange_det, abs_mul, ← pow_two, Real.sqrt_sq (abs_nonneg _),
    Real.sq_sqrt (abs_nonneg _)]

/-- Identical coordinate changes commute with rotations between the copies. -/
theorem bosonLinearChange_rotate (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (θ : ℝ) (z : BosonConfig m) :
    bosonLinearChange m A (bosonRotate θ z) = bosonRotate θ (bosonLinearChange m A z) := by
  have h0 : bosonPosition 0 (bosonLinearChange m A (bosonRotate θ z)) =
      bosonPosition 0 (bosonRotate θ (bosonLinearChange m A z)) := by
    simp only [bosonPosition_linearChange_zero, bosonPosition_rotate_zero,
      bosonPosition_linearChange_one, map_add, map_smul]
  have h1 : bosonPosition 1 (bosonLinearChange m A (bosonRotate θ z)) =
      bosonPosition 1 (bosonRotate θ (bosonLinearChange m A z)) := by
    simp only [bosonPosition_linearChange_one, bosonPosition_rotate_one,
      bosonPosition_linearChange_zero, map_add, map_smul]
  ext ⟨i,j⟩
  fin_cases i
  · exact congrArg (fun x : WaveConfig m => x j) h0
  · exact congrArg (fun x : WaveConfig m => x j) h1

/-- The physical pullbacks commute on every two-copy L² wavefunction. -/
theorem schrodingerRotation_linearChange (m : ℕ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (θ : ℝ) (f : SchrodingerSpace m) :
    schrodingerRotation m θ (linearCoordinateChange (bosonLinearChange m A) f) =
      linearCoordinateChange (bosonLinearChange m A) (schrodingerRotation m θ f) := by
  apply Lp.ext
  filter_upwards [schrodingerRotation_coeFn m θ (linearCoordinateChange (bosonLinearChange m A) f),
    (bosonRotation_measurePreserving m θ).quasiMeasurePreserving.ae_eq_comp
      (linearCoordinateChange_coeFn (bosonLinearChange m A) f),
    linearCoordinateChange_coeFn (bosonLinearChange m A) (schrodingerRotation m θ f),
    (linearCoordinateChange_quasiMeasurePreserving (bosonLinearChange m A)).ae_eq_comp
      (schrodingerRotation_coeFn m θ f)] with z h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂ h₄
  rw [h₁, h₂, h₃, h₄, bosonLinearChange_rotate]

attribute [local irreducible] linearCoordinateChange

/-- Tensoring the normalized coordinate change gives the normalized pullback
by the block coordinate change. -/
theorem waveTensor_linearChange (m : ℕ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (v : HilbertSquare (WaveSpace m)) :
    waveTensor m (hilbertTensorMap
      (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap
      (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap v) =
    linearCoordinateChange (bosonLinearChange m A) (waveTensor m v) := by
  have h : (waveTensor m).toContinuousLinearMap.comp (hilbertTensorMap
      (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap
      (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap) =
      (linearCoordinateChange (bosonLinearChange m A)).toLinearIsometry.toContinuousLinearMap.comp
        (waveTensor m).toContinuousLinearMap := by
    apply hilbertTensor_ext
    intro f g
    simp only [ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    apply Lp.ext
    have h0 : QuasiMeasurePreserving (bosonPosition (m := m) 0) volume volume :=
      quasiMeasurePreserving_fst.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
    have h1 : QuasiMeasurePreserving (bosonPosition (m := m) 1) volume volume :=
      quasiMeasurePreserving_snd.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
    filter_upwards [waveTensor_tmul_coeFn m (waveLinearChange m A f) (waveLinearChange m A g),
      h0.ae_eq_comp (waveLinearChange_coeFn m A f),
      h1.ae_eq_comp (waveLinearChange_coeFn m A g),
      linearCoordinateChange_coeFn (bosonLinearChange m A) (waveTensor m (hilbertTmul f g)),
      (linearCoordinateChange_quasiMeasurePreserving (bosonLinearChange m A)).ae_eq_comp
        (waveTensor_tmul_coeFn m f g)] with z hT hf hg hP hT'
    simp only [Function.comp_apply] at hf hg hT'
    have hleft := hT.trans (congrArg₂ (fun a b : ℂ => a * b) hf hg)
    have hright := hP.trans (congrArg
      (fun a : ℂ => (linearCoordinateChangeScale (bosonLinearChange m A) : ℂ) * a) hT')
    apply hleft.trans
    apply Eq.trans _ hright.symm
    rw [bosonLinearChange_scale]
    simp only [bosonPosition_linearChange_zero, bosonPosition_linearChange_one]
    push_cast
    ring
  exact congrArg (fun B => B v) h

/-- Identical Jacobian-normalized position changes commute with copy rotations
on the completed tensor product, including arbitrary invertible squeezes. -/
theorem schrodingerTensorRotation_linearChange (m : ℕ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (θ : ℝ)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorRotation m θ (hilbertTensorMap
      (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap
      (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap v) =
    hilbertTensorMap (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap
      (waveLinearChange m A).toLinearIsometry.toContinuousLinearMap
      (schrodingerTensorRotation m θ v) := by
  apply (waveTensorEquiv m).injective
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, waveTensorEquiv_apply]
  rw [waveTensor_linearChange, waveTensor_linearChange]
  simp only [← waveTensorEquiv_apply, LinearIsometryEquiv.apply_symm_apply]
  exact schrodingerRotation_linearChange m A θ _

end
end GaussianTesting
