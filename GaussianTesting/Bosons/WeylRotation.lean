module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PureCharacteristic
public import GaussianTesting.Bosons.SchrodingerFourCopy

@[expose] public section

/-!
# Weyl displacements under copy rotations

The two-copy Weyl action is the tensor product of the explicit one-copy
unitaries. Coordinate changes prove the displacement-rotation identity in
Section 6 on the full completed tensor square.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

/-- Join two one-copy position vectors into the two-copy configuration. -/
def bosonJoin {m : ℕ} (x y : WaveConfig m) : BosonConfig m :=
  WithLp.toLp 2 fun ij => if ij.1 = 0 then x ij.2 else y ij.2

@[simp] theorem bosonPosition_join_zero {m : ℕ} (x y : WaveConfig m) :
    bosonPosition 0 (bosonJoin x y) = x := by ext j; simp [bosonJoin]

@[simp] theorem bosonPosition_join_one {m : ℕ} (x y : WaveConfig m) :
    bosonPosition 1 (bosonJoin x y) = y := by ext j; simp [bosonJoin]

@[simp] theorem bosonPosition_sub {m : ℕ} (i : Fin 2) (x y : BosonConfig m) :
    bosonPosition i (x-y) = bosonPosition i x - bosonPosition i y := by ext j; rfl

@[simp] theorem bosonPosition_rotate_zero {m : ℕ} (θ : ℝ) (z : BosonConfig m) :
    bosonPosition 0 (bosonRotate θ z) =
      Real.cos θ • bosonPosition 0 z + Real.sin θ • bosonPosition 1 z := by
  ext j; simp

@[simp] theorem bosonPosition_rotate_one {m : ℕ} (θ : ℝ) (z : BosonConfig m) :
    bosonPosition 1 (bosonRotate θ z) =
      -Real.sin θ • bosonPosition 0 z + Real.cos θ • bosonPosition 1 z := by
  ext j; simp

private theorem continuous_bosonPosition {m : ℕ} (i : Fin 2) :
    Continuous (bosonPosition (m := m) i) := by
  unfold bosonPosition
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
  fun_prop

private theorem pairWeyl_memLp {m : ℕ} (r s : WavePhase m) (f : SchrodingerSpace m) :
    MemLp (fun z => weylPhase r (bosonPosition 0 z) * weylPhase s (bosonPosition 1 z) *
      f (z - bosonJoin r.1 s.1)) 2 volume := by
  have hmp : MeasurePreserving (fun z : BosonConfig m => z - bosonJoin r.1 s.1) :=
    measurePreserving_sub_right volume _
  apply ((Lp.memLp f).comp_measurePreserving hmp).congr_norm
  · have hc (t : WavePhase m) (i : Fin 2) :
        Continuous (fun z : BosonConfig m => weylPhase t (bosonPosition i z)) :=
      (continuous_weylPhase m).comp (continuous_const.prodMk (continuous_bosonPosition i))
    exact ((hc r 0).aestronglyMeasurable.mul (hc s 1).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving)
  · exact Filter.Eventually.of_forall fun z => by simp

/-- Apply one Weyl displacement to each position factor. -/
def pairWeylApply {m : ℕ} (r s : WavePhase m) (f : SchrodingerSpace m) :
    SchrodingerSpace m :=
  ((by exact pairWeyl_memLp r s f) :
    MemLp (fun z => weylPhase r (bosonPosition 0 z) * weylPhase s (bosonPosition 1 z) *
      f (z - bosonJoin r.1 s.1)) 2 volume).toLp _

private theorem pairWeylApply_coeFn {m : ℕ} (r s : WavePhase m) (f : SchrodingerSpace m) :
    (pairWeylApply r s f : BosonConfig m → ℂ) =ᵐ[volume]
      fun z => weylPhase r (bosonPosition 0 z) * weylPhase s (bosonPosition 1 z) *
        f (z - bosonJoin r.1 s.1) := (pairWeyl_memLp r s f).coeFn_toLp

/-- The paired Weyl action bundled as a complex linear map. -/
def pairWeylLinear {m : ℕ} (r s : WavePhase m) :
    SchrodingerSpace m →ₗ[ℂ] SchrodingerSpace m where
  toFun := pairWeylApply r s
  map_add' f g := by
    apply Lp.ext
    have hmp : MeasurePreserving (fun z : BosonConfig m => z - bosonJoin r.1 s.1) :=
      measurePreserving_sub_right volume _
    filter_upwards [pairWeylApply_coeFn r s (f+g), pairWeylApply_coeFn r s f,
      pairWeylApply_coeFn r s g, Lp.coeFn_add (pairWeylApply r s f) (pairWeylApply r s g),
      hmp.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add f g)] with z h h₁ h₂ h₃ h₄
    simp only [Function.comp_apply, Pi.add_apply] at h₄
    simp only [h, h₃, h₁, h₂, h₄, Pi.add_apply, mul_add]
  map_smul' c f := by
    change pairWeylApply r s (c • f) = c • pairWeylApply r s f
    apply Lp.ext
    have hmp : MeasurePreserving (fun z : BosonConfig m => z - bosonJoin r.1 s.1) :=
      measurePreserving_sub_right volume _
    filter_upwards [pairWeylApply_coeFn r s (c • f), pairWeylApply_coeFn r s f,
      Lp.coeFn_smul c (pairWeylApply r s f),
      hmp.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c f)] with z h h₁ h₂ h₃
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h₃
    simp only [h, h₂, h₁, h₃, Pi.smul_apply, smul_eq_mul, mul_left_comm]

private theorem pairWeylApply_norm {m : ℕ} (r s : WavePhase m) (f : SchrodingerSpace m) :
    ‖pairWeylApply r s f‖ = ‖f‖ := by
  let T : SchrodingerSpace m →ₗᵢ[ℂ] SchrodingerSpace m := Lp.compMeasurePreservingₗᵢ ℂ (fun z : BosonConfig m => z - bosonJoin r.1 s.1)
    (measurePreserving_sub_right volume _)
  calc
    _ = ‖T f‖ := by
      rw [Lp.norm_def, Lp.norm_def]
      congr 1
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      filter_upwards [pairWeylApply_coeFn r s f,
        Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume (bosonJoin r.1 s.1))]
        with z h₁ h₂
      change ‖pairWeylApply r s f z‖ = ‖Lp.compMeasurePreserving
        (fun z : BosonConfig m => z - bosonJoin r.1 s.1)
        (measurePreserving_sub_right volume _) f z‖
      simp only [h₁, h₂, norm_mul, weylPhase_norm, one_mul, Function.comp_apply]
    _ = ‖f‖ := T.norm_map f

/-- The explicit two-copy Weyl operator, before identifying it with a tensor product. -/
def schrodingerWeyl (m : ℕ) (r s : WavePhase m) :
    SchrodingerSpace m →L[ℂ] SchrodingerSpace m :=
  (pairWeylLinear r s).mkContinuous 1 (fun f => by
    change ‖pairWeylApply r s f‖ ≤ 1 * ‖f‖
    rw [pairWeylApply_norm, one_mul])

theorem schrodingerWeyl_coeFn (m : ℕ) (r s : WavePhase m) (f : SchrodingerSpace m) :
    (schrodingerWeyl m r s f : BosonConfig m → ℂ) =ᵐ[volume]
      fun z => weylPhase r (bosonPosition 0 z) * weylPhase s (bosonPosition 1 z) *
        f (z - bosonJoin r.1 s.1) := pairWeylApply_coeFn r s f

/-- The two-copy displacement is the tensor product of the one-copy Weyl operators. -/
theorem schrodingerWeyl_waveTensor (m : ℕ) (r s : WavePhase m)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerWeyl m r s (waveTensor m v) =
      waveTensor m (hilbertTensorMap
        (weylOperator m r).toLinearIsometry.toContinuousLinearMap
        (weylOperator m s).toLinearIsometry.toContinuousLinearMap v) := by
  have h : (schrodingerWeyl m r s).comp (waveTensor m).toContinuousLinearMap =
      (waveTensor m).toContinuousLinearMap.comp (hilbertTensorMap
        (weylOperator m r).toLinearIsometry.toContinuousLinearMap
        (weylOperator m s).toLinearIsometry.toContinuousLinearMap) := by
    apply hilbertTensor_ext
    intro f g
    simp only [ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    apply Lp.ext
    have hmp : MeasurePreserving (fun z : BosonConfig m => z - bosonJoin r.1 s.1) :=
      measurePreserving_sub_right volume _
    have h0 : QuasiMeasurePreserving (bosonPosition (m := m) 0) volume volume :=
      quasiMeasurePreserving_fst.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
    have h1 : QuasiMeasurePreserving (bosonPosition (m := m) 1) volume volume :=
      quasiMeasurePreserving_snd.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
    filter_upwards [schrodingerWeyl_coeFn m r s (waveTensor m (hilbertTmul f g)),
      hmp.quasiMeasurePreserving.ae_eq_comp (waveTensor_tmul_coeFn m f g),
      waveTensor_tmul_coeFn m (weylOperator m r f) (weylOperator m s g),
      h0.ae_eq_comp (weylOperator_coeFn m r f),
      h1.ae_eq_comp (weylOperator_coeFn m s g)] with z h hT hT' hf hg
    simp only [Function.comp_apply] at hT hf hg
    rw [h, hT, hT', hf, hg]
    simp only [bosonPosition_sub, bosonPosition_join_zero, bosonPosition_join_one]
    ring
  exact congrArg (fun A => A v) h


private theorem weylPhase_rotation_real {m : ℕ} (a b : ℝ) (h : a^2+b^2=1)
    (r s : WavePhase m) (x y : WaveConfig m) :
    inner ℝ r.2 (a • x + b • y) - inner ℝ r.2 r.1 / 2 +
      (inner ℝ s.2 (-b • x + a • y) - inner ℝ s.2 s.1 / 2) =
    inner ℝ (a • r.2 - b • s.2) x -
      inner ℝ (a • r.2 - b • s.2) (a • r.1 - b • s.1) / 2 +
      (inner ℝ (b • r.2 + a • s.2) y -
        inner ℝ (b • r.2 + a • s.2) (b • r.1 + a • s.1) / 2) := by
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, inner_smul_right]
  linear_combination ((inner ℝ r.2 r.1 + inner ℝ s.2 s.1) / 2) * h

private theorem weylPhase_rotation {m : ℕ} (θ : ℝ) (r s : WavePhase m)
    (z : BosonConfig m) :
    weylPhase r (bosonPosition 0 (bosonRotate θ z)) *
      weylPhase s (bosonPosition 1 (bosonRotate θ z)) =
    weylPhase (Real.cos θ • r - Real.sin θ • s) (bosonPosition 0 z) *
      weylPhase (Real.sin θ • r + Real.cos θ • s) (bosonPosition 1 z) := by
  simp only [weylPhase, ← Complex.exp_add, bosonPosition_rotate_zero,
    bosonPosition_rotate_one, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  congr 1
  rw [← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 2
  exact weylPhase_rotation_real (Real.cos θ) (Real.sin θ)
    (by nlinarith [Real.sin_sq_add_cos_sq θ]) r s _ _

private theorem bosonRotate_sub_join {m : ℕ} (θ : ℝ) (q q' : WaveConfig m)
    (z : BosonConfig m) :
    bosonRotate θ (z - bosonJoin (Real.cos θ • q - Real.sin θ • q')
      (Real.sin θ • q + Real.cos θ • q')) = bosonRotate θ z - bosonJoin q q' := by
  have h := Real.sin_sq_add_cos_sq θ
  ext ⟨i,j⟩
  fin_cases i <;> simp [bosonJoin]
  · nlinarith [congrArg (fun t : ℝ => t * q j) h]
  · nlinarith [congrArg (fun t : ℝ => t * q' j) h]

/-- Coordinate pullback proves Weyl covariance for every copy-rotation angle. -/
theorem schrodingerRotation_weyl (m : ℕ) (θ : ℝ) (r s : WavePhase m)
    (f : SchrodingerSpace m) :
    schrodingerRotation m θ (schrodingerWeyl m r s f) =
      schrodingerWeyl m (Real.cos θ • r - Real.sin θ • s)
        (Real.sin θ • r + Real.cos θ • s) (schrodingerRotation m θ f) := by
  apply Lp.ext
  let r' := Real.cos θ • r - Real.sin θ • s
  let s' := Real.sin θ • r + Real.cos θ • s
  have hmp : MeasurePreserving (fun z : BosonConfig m => z - bosonJoin r'.1 s'.1) :=
    measurePreserving_sub_right volume _
  filter_upwards [schrodingerRotation_coeFn m θ (schrodingerWeyl m r s f),
    (bosonRotation_measurePreserving m θ).quasiMeasurePreserving.ae_eq_comp
      (schrodingerWeyl_coeFn m r s f),
    schrodingerWeyl_coeFn m r' s' (schrodingerRotation m θ f),
    hmp.quasiMeasurePreserving.ae_eq_comp (schrodingerRotation_coeFn m θ f)]
    with z h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂ h₄
  rw [h₁, h₂, h₃, h₄, weylPhase_rotation]
  congr 1
  exact congrArg (fun t => f t) (bosonRotate_sub_join θ r.1 s.1 z).symm


/-- Displacements acting independently on the two completed tensor factors. -/
def tensorWeylOperator (m : ℕ) (r s : WavePhase m) :
    HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) :=
  hilbertTensorMap (weylOperator m r).toLinearIsometry.toContinuousLinearMap
    (weylOperator m s).toLinearIsometry.toContinuousLinearMap

@[simp] theorem tensorWeylOperator_tmul (m : ℕ) (r s : WavePhase m)
    (f g : WaveSpace m) :
    tensorWeylOperator m r s (hilbertTmul f g) =
      hilbertTmul (weylOperator m r f) (weylOperator m s g) :=
  hilbertTensorMap_tmul _ _ _ _

/-- Copy rotations intertwine the tensor product of the explicit Weyl operators. -/
theorem schrodingerTensorRotation_weyl (m : ℕ) (θ : ℝ) (r s : WavePhase m)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorRotation m θ (tensorWeylOperator m r s v) =
      tensorWeylOperator m (Real.cos θ • r - Real.sin θ • s)
        (Real.sin θ • r + Real.cos θ • s) (schrodingerTensorRotation m θ v) := by
  apply (waveTensorEquiv m).injective
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, waveTensorEquiv_apply]
  unfold tensorWeylOperator
  rw [← schrodingerWeyl_waveTensor]
  change _ = waveTensor m (hilbertTensorMap _ _ _)
  rw [← schrodingerWeyl_waveTensor]
  simp only [← waveTensorEquiv_apply, LinearIsometryEquiv.apply_symm_apply]
  exact schrodingerRotation_weyl m θ r s _

private theorem sqrt_two_div_two : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
  have hpos : 0 < Real.sqrt 2 := by positivity
  rw [← one_div]
  apply (eq_div_iff (ne_of_gt hpos)).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The manuscript's displacement-rotation formula, as an equality on every
vector of the completed tensor square. -/
theorem schrodingerTensorRotation_balanced_weyl (m : ℕ) (r s : WavePhase m)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorRotation m (Real.pi / 4)
      (tensorWeylOperator m r s ((schrodingerTensorRotation m (Real.pi / 4)).symm v)) =
      tensorWeylOperator m ((Real.sqrt 2)⁻¹ • (r-s)) ((Real.sqrt 2)⁻¹ • (r+s)) v := by
  rw [schrodingerTensorRotation_weyl, LinearIsometryEquiv.apply_symm_apply]
  simp only [Real.cos_pi_div_four, Real.sin_pi_div_four, sqrt_two_div_two,
    smul_sub, smul_add]

/-- The Weyl expectation of a two-copy state. -/
def pureTensorCharacteristic (m : ℕ) (v : HilbertSquare (WaveSpace m))
    (r s : WavePhase m) : ℂ := inner ℂ v (tensorWeylOperator m r s v)

/-- Characteristic functions multiply on product wavefunctions. -/
theorem pureTensorCharacteristic_tmul (m : ℕ) (f g : WaveSpace m)
    (r s : WavePhase m) :
    pureTensorCharacteristic m (hilbertTmul f g) r s =
      pureWaveCharacteristic m f r * pureWaveCharacteristic m g s := by
  simp only [pureTensorCharacteristic, tensorWeylOperator_tmul, inner_hilbertTmul,
    pureWaveCharacteristic]

/-- The characteristic function transforms by the same phase-space rotation. -/
theorem pureTensorCharacteristic_inverse_rotation (m : ℕ) (θ : ℝ)
    (v : HilbertSquare (WaveSpace m)) (r s : WavePhase m) :
    pureTensorCharacteristic m ((schrodingerTensorRotation m θ).symm v) r s =
      pureTensorCharacteristic m v (Real.cos θ • r - Real.sin θ • s)
        (Real.sin θ • r + Real.cos θ • s) := by
  unfold pureTensorCharacteristic
  rw [← (schrodingerTensorRotation m θ).inner_map_map,
    schrodingerTensorRotation_weyl, LinearIsometryEquiv.apply_symm_apply]

/-- Product input followed by the inverse balanced splitter has the
characteristic-function identity used in Proposition 6.3. -/
theorem pureTensorCharacteristic_balanced_product (m : ℕ) (f g : WaveSpace m)
    (r s : WavePhase m) :
    pureTensorCharacteristic m
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul f g)) r s =
      pureWaveCharacteristic m f ((Real.sqrt 2)⁻¹ • (r-s)) *
        pureWaveCharacteristic m g ((Real.sqrt 2)⁻¹ • (r+s)) := by
  rw [pureTensorCharacteristic_inverse_rotation, pureTensorCharacteristic_tmul]
  simp only [Real.cos_pi_div_four, Real.sin_pi_div_four, sqrt_two_div_two,
    smul_sub, smul_add]

end
end GaussianTesting
