module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerRotation
public import GaussianTesting.GradientFlow.HilbertTensor
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Tensor products and parity of Schrödinger wavefunctions

Elementary tensors are the actual products of the one-copy wavefunctions.
Fubini's theorem identifies their inner products, so this realization extends
isometrically to the completed Hilbert tensor square. The quarter-turn is the
signed swap on this embedding, as used in Lemma 6.2.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace TensorProduct

noncomputable section

/-- The position space of `m` bosonic modes. -/
abbrev WaveConfig (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The one-copy Schrödinger Hilbert space. -/
abbrev WaveSpace (m : ℕ) := Lp ℂ 2 (volume : Measure (WaveConfig m))

/-- The positions in one of the two copies. -/
def bosonPosition {m : ℕ} (i : Fin 2) (z : BosonConfig m) : WaveConfig m :=
  WithLp.toLp 2 fun j => z (i, j)

@[simp] theorem bosonPosition_apply {m : ℕ} (i : Fin 2) (z : BosonConfig m) (j : Fin m) :
    bosonPosition i z j = z (i, j) := rfl

/-- The linear equivalence splitting a two-copy position configuration. -/
def splitConfig (m : ℕ) :
    BosonConfig m ≃ₗ[ℝ] WithLp 2 (WaveConfig m × WaveConfig m) where
  toFun z := WithLp.toLp 2 (bosonPosition 0 z, bosonPosition 1 z)
  invFun xy := WithLp.toLp 2 fun p => if p.1 = 0 then xy.fst p.2 else xy.snd p.2
  left_inv z := by
    ext ⟨i, j⟩
    fin_cases i <;> simp [bosonPosition]
  right_inv xy := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext j <;> simp [bosonPosition]
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext j <;> simp [bosonPosition]
  map_smul' a x := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext j <;> simp [bosonPosition]

def splitConfigIsometry (m : ℕ) :
    BosonConfig m ≃ₗᵢ[ℝ] WithLp 2 (WaveConfig m × WaveConfig m) where
  toLinearEquiv := splitConfig m
  norm_map' z := by
    have h : ‖splitConfig m z‖ ^ 2 = ‖z‖ ^ 2 := by
      simp only [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq,
        Fintype.sum_prod_type, Fin.sum_univ_two]
      rfl
    nlinarith [norm_nonneg (splitConfig m z), norm_nonneg z]

/-- Splitting the two sets of positions preserves Lebesgue product measure. -/
theorem bosonPositions_measurePreserving (m : ℕ) :
    MeasurePreserving (fun z : BosonConfig m => (bosonPosition 0 z, bosonPosition 1 z))
      volume (volume.prod volume) := by
  exact (WithLp.volume_preserving_ofLp (WaveConfig m) (WaveConfig m)).comp
    (splitConfigIsometry m).measurePreserving

abbrev ProductWaveSpace (m : ℕ) :=
  Lp ℂ 2 ((volume : Measure (WaveConfig m)).prod (volume : Measure (WaveConfig m)))

private theorem productWave_memLp {m : ℕ} (f g : WaveSpace m) :
    MemLp (fun z : WaveConfig m × WaveConfig m => f z.1 * g z.2) 2
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun z : WaveConfig m × WaveConfig m => f z.1 * g z.2)
      (volume.prod volume) :=
    ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      quasiMeasurePreserving_fst).mul
        ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving quasiMeasurePreserving_snd)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_mul, mul_pow] using
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)).mul_prod
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g))

def productWave {m : ℕ} (f g : WaveSpace m) : ProductWaveSpace m :=
  ((by exact productWave_memLp f g) :
    MemLp (fun z : WaveConfig m × WaveConfig m => f z.1 * g z.2) 2
      (volume.prod volume)).toLp _

theorem productWave_coeFn {m : ℕ} (f g : WaveSpace m) :
    (productWave f g : WaveConfig m × WaveConfig m → ℂ) =ᵐ[volume.prod volume]
      fun z => f z.1 * g z.2 := (productWave_memLp f g).coeFn_toLp

private theorem inner_productWave {m : ℕ} (f g f' g' : WaveSpace m) :
    inner ℂ (productWave f g) (productWave f' g') = inner ℂ f f' * inner ℂ g g' := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [productWave_coeFn f g, productWave_coeFn f' g'] with z h h'
  rw [h, h']
  simp only [RCLike.inner_apply, map_mul]
  ring

private theorem productWave_add_left {m : ℕ} (f f' g : WaveSpace m) :
    productWave (f + f') g = productWave f g + productWave f' g := by
  apply Lp.ext
  filter_upwards [productWave_coeFn (f + f') g, productWave_coeFn f g,
    productWave_coeFn f' g, Lp.coeFn_add (productWave f g) (productWave f' g),
    quasiMeasurePreserving_fst.ae (Lp.coeFn_add f f')] with z h h' h'' ha hf
  simp only [h, ha, h', h'', hf, Pi.add_apply, add_mul]

private theorem productWave_smul_left {m : ℕ} (a : ℂ) (f g : WaveSpace m) :
    productWave (a • f) g = a • productWave f g := by
  apply Lp.ext
  filter_upwards [productWave_coeFn (a • f) g, productWave_coeFn f g,
    Lp.coeFn_smul a (productWave f g),
    quasiMeasurePreserving_fst.ae (Lp.coeFn_smul a f)] with z h h' ha hf
  simp only [h, ha, h', hf, Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem productWave_add_right {m : ℕ} (f g g' : WaveSpace m) :
    productWave f (g + g') = productWave f g + productWave f g' := by
  apply Lp.ext
  filter_upwards [productWave_coeFn f (g + g'), productWave_coeFn f g,
    productWave_coeFn f g', Lp.coeFn_add (productWave f g) (productWave f g'),
    quasiMeasurePreserving_snd.ae (Lp.coeFn_add g g')] with z h h' h'' ha hg
  simp only [h, ha, h', h'', hg, Pi.add_apply, mul_add]

private theorem productWave_smul_right {m : ℕ} (a : ℂ) (f g : WaveSpace m) :
    productWave f (a • g) = a • productWave f g := by
  apply Lp.ext
  filter_upwards [productWave_coeFn f (a • g), productWave_coeFn f g,
    Lp.coeFn_smul a (productWave f g),
    quasiMeasurePreserving_snd.ae (Lp.coeFn_smul a g)] with z h h' ha hg
  simp only [h, ha, h', hg, Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- Pointwise multiplication of two wavefunctions as a bilinear map. -/
def productWaveLinear (m : ℕ) :
    WaveSpace m →ₗ[ℂ] WaveSpace m →ₗ[ℂ] ProductWaveSpace m :=
  LinearMap.mk₂ ℂ productWave (by exact productWave_add_left) (by exact productWave_smul_left)
    (by exact productWave_add_right) (by exact fun a f g => productWave_smul_right a f g)

/-- The linear map induced by pointwise products on the algebraic tensor square. -/
def productWaveTensorLinear (m : ℕ) :
    WaveSpace m ⊗[ℂ] WaveSpace m →ₗ[ℂ] ProductWaveSpace m :=
  TensorProduct.lift (productWaveLinear m)

def productWaveTensorIsometry (m : ℕ) :
    WaveSpace m ⊗[ℂ] WaveSpace m →ₗᵢ[ℂ] ProductWaveSpace m :=
  (productWaveTensorLinear m).isometryOfInner fun u v => by
    induction u using TensorProduct.inductionOn with
    | tmul f g =>
      induction v using TensorProduct.inductionOn with
      | tmul f' g' =>
        exact (inner_productWave f g f' g').trans (TensorProduct.inner_tmul ℂ f f' g g').symm
      | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]

/-- The canonical isometric embedding of the completed tensor square into
actual two-copy wavefunctions. -/
def waveTensor (m : ℕ) : HilbertSquare (WaveSpace m) →ₗᵢ[ℂ] SchrodingerSpace m :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (bosonPositions_measurePreserving m)).comp
    (productWaveTensorIsometry m).fromCompletion

/-- Elementary tensors are pointwise products of the one-copy functions. -/
theorem waveTensor_tmul_coeFn (m : ℕ) (f g : WaveSpace m) :
    (waveTensor m (hilbertTmul f g) : BosonConfig m → ℂ) =ᵐ[volume]
      fun z => f (bosonPosition 0 z) * g (bosonPosition 1 z) := by
  change Lp.compMeasurePreserving _ _
    ((productWaveTensorIsometry m).fromCompletion (hilbertTmul f g)) =ᵐ[volume] _
  rw [show (productWaveTensorIsometry m).fromCompletion (hilbertTmul f g) = productWave f g
    from (productWaveTensorIsometry m).fromCompletion_apply_coe (f ⊗ₜ[ℂ] g)]
  exact (Lp.coeFn_compMeasurePreserving (productWave f g)
    (bosonPositions_measurePreserving m)).trans
    ((bosonPositions_measurePreserving m).quasiMeasurePreserving.ae_eq_comp
      (productWave_coeFn f g))

/-- Multiplication of wavefunctions on separate copies as a continuous
complex-bilinear map. -/
def waveProduct (m : ℕ) : WaveSpace m →L[ℂ] WaveSpace m →L[ℂ] SchrodingerSpace m :=
  (ContinuousLinearMap.compL ℂ (WaveSpace m) (HilbertSquare (WaveSpace m))
    (SchrodingerSpace m) (waveTensor m).toContinuousLinearMap).comp hilbertTmul

@[simp] theorem waveProduct_apply (m : ℕ) (f g : WaveSpace m) :
    waveProduct m f g = waveTensor m (hilbertTmul f g) := rfl

/-- The product formula for Hilbert inner products holds for actual
Schrödinger wavefunctions. -/
@[simp] theorem inner_waveProduct (m : ℕ) (f g f' g' : WaveSpace m) :
    inner ℂ (waveProduct m f g) (waveProduct m f' g') =
      inner ℂ f f' * inner ℂ g g' := by
  exact ((waveTensor m).inner_map_map (hilbertTmul f g) (hilbertTmul f' g')).trans
    (inner_hilbertTmul f f' g g')

private theorem waveNeg_measurePreserving (m : ℕ) :
    MeasurePreserving (fun x : WaveConfig m => -x) :=
  (LinearIsometryEquiv.neg ℝ : WaveConfig m ≃ₗᵢ[ℝ] WaveConfig m).measurePreserving

private theorem parity_pullback_involution (m : ℕ) (f : WaveSpace m) :
    Lp.compMeasurePreserving (fun x : WaveConfig m => -x) (waveNeg_measurePreserving m)
      (Lp.compMeasurePreserving (fun x : WaveConfig m => -x)
        (waveNeg_measurePreserving m) f) = f := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (fun x : WaveConfig m => -x) ∘ (fun x : WaveConfig m => -x) = id :=
    funext neg_neg
  simp only [h, Lp.compMeasurePreserving_id_apply]

/-- The manuscript's reflection `J f(x) = f(-x)` as a unitary on the
one-copy Schrödinger Hilbert space. -/
def waveParity (m : ℕ) : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : WaveConfig m => -x) (by exact waveNeg_measurePreserving m))
    (Lp.compMeasurePreservingₗ ℂ (fun x : WaveConfig m => -x) (by exact waveNeg_measurePreserving m))
    (by ext f : 1; exact parity_pullback_involution m f)
    (by ext f : 1; exact parity_pullback_involution m f)

theorem waveParity_coeFn (m : ℕ) (f : WaveSpace m) :
    (waveParity m f : WaveConfig m → ℂ) =ᵐ[volume] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f (waveNeg_measurePreserving m)

@[simp] theorem waveParity_involution (m : ℕ) (f : WaveSpace m) :
    waveParity m (waveParity m f) = f := parity_pullback_involution m f

@[simp] theorem bosonPosition_quarter_zero {m : ℕ} (z : BosonConfig m) :
    bosonPosition 0 (bosonRotate (Real.pi / 2) z) = bosonPosition 1 z := by
  ext j
  simp

@[simp] theorem bosonPosition_quarter_one {m : ℕ} (z : BosonConfig m) :
    bosonPosition 1 (bosonRotate (Real.pi / 2) z) = -bosonPosition 0 z := by
  ext j
  simp

/-- The physical quarter-turn acts as reflection and swap on elementary
tensors. No Hermite-basis identification is assumed. -/
theorem schrodingerRotation_quarter_waveTensor (m : ℕ) (f g : WaveSpace m) :
    schrodingerRotation m (Real.pi / 2) (waveTensor m (hilbertTmul f g)) =
      waveTensor m (hilbertTmul (waveParity m g) f) := by
  apply Lp.ext
  have hp : QuasiMeasurePreserving (bosonPosition (m := m) 0) volume volume :=
    quasiMeasurePreserving_fst.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
  filter_upwards [schrodingerRotation_coeFn m (Real.pi / 2)
      (waveTensor m (hilbertTmul f g)),
    (bosonRotation_measurePreserving m (Real.pi / 2)).quasiMeasurePreserving.ae_eq_comp
      (waveTensor_tmul_coeFn m f g),
    waveTensor_tmul_coeFn m (waveParity m g) f,
    hp.ae_eq_comp (waveParity_coeFn m g)] with z hU hfg hJf hJ
  calc
    _ = waveTensor m (hilbertTmul f g) (bosonRotate (Real.pi / 2) z) := hU
    _ = f (bosonPosition 0 (bosonRotate (Real.pi / 2) z)) *
        g (bosonPosition 1 (bosonRotate (Real.pi / 2) z)) := hfg
    _ = f (bosonPosition 1 z) * g (-bosonPosition 0 z) := by
      rw [bosonPosition_quarter_zero, bosonPosition_quarter_one]
    _ = waveParity m g (bosonPosition 0 z) * f (bosonPosition 1 z) := by
      rw [show waveParity m g (bosonPosition 0 z) = g (-bosonPosition 0 z) from hJ]
      exact mul_comm _ _
    _ = _ := hJf.symm

/-- The signed-swap identity extends from elementary tensors to the entire
completed Hilbert tensor square. -/
theorem schrodingerRotation_quarter_waveTensor_apply (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerRotation m (Real.pi / 2) (waveTensor m v) =
      waveTensor m (hilbertTensorMap (waveParity m).toLinearIsometry.toContinuousLinearMap
        (ContinuousLinearMap.id ℂ (WaveSpace m)) (hilbertSwap v)) := by
  let A := hilbertTensorMap (waveParity m).toLinearIsometry.toContinuousLinearMap
    (ContinuousLinearMap.id ℂ (WaveSpace m))
  refine hilbertTensor_induction (p := fun w =>
    schrodingerRotation m (Real.pi / 2) (waveTensor m w) = waveTensor m (A (hilbertSwap w)))
    (isClosed_eq ((schrodingerRotation m (Real.pi / 2)).continuous.comp (waveTensor m).continuous)
      ((waveTensor m).continuous.comp (A.continuous.comp hilbertSwap.continuous))) ?_ ?_ v
  · intro f g
    have hs : A (hilbertSwap (hilbertTmul f g)) = hilbertTmul (waveParity m g) f :=
      (congrArg A (hilbertSwap_tmul f g)).trans (hilbertTensorMap_tmul _ _ g f)
    exact (schrodingerRotation_quarter_waveTensor m f g).trans
      (congrArg (waveTensor m) hs).symm
  · intro a b ha hb
    simp only [map_add, ha, hb]

end
end GaussianTesting
