module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.FourierAction
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Normed.Lp.SmoothApprox

@[expose] public section

/-!
# Tensor products and rotations for the Fourier Gaussian unitary

The tensor product of two one-copy Fourier transforms is the Fourier
transform of the joint position coordinates, and it commutes with copy rotations.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure Set
open scoped InnerProductSpace FourierTransform ContDiff

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true

/-- The Fourier transform on the actual two-copy wavefunction space. -/
def schrodingerFourier (m : ℕ) : SchrodingerSpace m ≃ₗᵢ[ℂ] SchrodingerSpace m :=
  Lp.fourierTransformₗᵢ (BosonConfig m) ℂ

private theorem rotation_schwartz_toLp (m : ℕ) (θ : ℝ)
    (f : SchwartzMap (BosonConfig m) ℂ) :
    schrodingerRotation m θ (f.toLp 2 volume) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (bosonRotation m θ).toContinuousLinearEquiv f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [schrodingerRotation_coeFn m θ (f.toLp 2 volume),
    (bosonRotation_measurePreserving m θ).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2 volume),
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (bosonRotation m θ).toContinuousLinearEquiv f).coeFn_toLp 2 volume] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃]
  rfl

/-- The joint Fourier transform commutes with the orthogonal position rotation. -/
theorem schrodingerFourier_rotation (m : ℕ) (θ : ℝ) (f : SchrodingerSpace m) :
    schrodingerFourier m (schrodingerRotation m θ f) =
      schrodingerRotation m θ (schrodingerFourier m f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := BosonConfig m) (F := ℂ)
    (p := 2) (μ := volume) ENNReal.ofNat_ne_top).induction_on
    (p := fun f : SchrodingerSpace m =>
      schrodingerFourier m (schrodingerRotation m θ f) =
        schrodingerRotation m θ (schrodingerFourier m f)) f ?_ ?_
  · exact isClosed_eq ((schrodingerFourier m).continuous.comp (schrodingerRotation m θ).continuous)
      ((schrodingerRotation m θ).continuous.comp (schrodingerFourier m).continuous)
  intro g
  change schrodingerFourier m (schrodingerRotation m θ (g.toLp 2 volume)) =
    schrodingerRotation m θ (schrodingerFourier m (g.toLp 2 volume))
  rw [rotation_schwartz_toLp]
  change 𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (bosonRotation m θ).toContinuousLinearEquiv g).toLp 2 volume) =
      schrodingerRotation m θ (𝓕 (g.toLp 2 volume))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (bosonRotation m θ).toContinuousLinearEquiv g)).coeFn_toLp 2 volume,
    schrodingerRotation_coeFn m θ ((𝓕 g).toLp 2 volume),
    (bosonRotation_measurePreserving m θ).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 g).coeFn_toLp 2 volume)] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃]
  exact Real.fourier_comp_linearIsometry (bosonRotation m θ) (g : BosonConfig m → ℂ) x

private theorem dense_compactSchwartz (m : ℕ) :
    DenseRange (fun f : {f : SchwartzMap (WaveConfig m) ℂ // HasCompactSupport (f : WaveConfig m → ℂ)} =>
      f.val.toLp 2 volume) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le
    (p := 2) ENNReal.ofNat_ne_top (by norm_num) (Lp.memLp f) hε
  let G : SchwartzMap (WaveConfig m) ℂ := hg₁.toSchwartzMap hg₂
  refine ⟨G.toLp 2 volume, ⟨⟨G, hg₁⟩, rfl⟩, ?_⟩
  have hae : (f : WaveConfig m → ℂ) - (G.toLp 2 volume : WaveConfig m → ℂ) =ᵐ[volume]
      (f : WaveConfig m → ℂ) - g := by
    filter_upwards [G.coeFn_toLp 2 volume] with x hx
    simp only [Pi.sub_apply, hx]
    rfl
  simp only [Metric.mem_closedBall', Lp.dist_def, eLpNorm_congr_ae hae]
  grw [hg₃, ENNReal.toReal_ofReal hε.le]
  simp

private theorem contDiff_bosonPosition (m : ℕ) (i : Fin 2) :
    ContDiff ℝ ∞ (bosonPosition (m := m) i) := by
  unfold bosonPosition
  apply PiLp.contDiff_toLp.comp
  fun_prop

private theorem continuous_bosonJoin (m : ℕ) :
    Continuous (fun p : WaveConfig m × WaveConfig m => bosonJoin p.1 p.2) := by
  unfold bosonJoin
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 × Fin m => ℝ)).comp
  apply continuous_pi
  rintro ⟨i,j⟩
  fin_cases i <;> simp <;> fun_prop

private theorem compact_product {m : ℕ} (f g : SchwartzMap (WaveConfig m) ℂ)
    (hf : HasCompactSupport (f : WaveConfig m → ℂ))
    (hg : HasCompactSupport (g : WaveConfig m → ℂ)) :
    HasCompactSupport (fun z : BosonConfig m => f (bosonPosition 0 z) * g (bosonPosition 1 z)) := by
  apply HasCompactSupport.intro ((hf.prod hg).image (continuous_bosonJoin m))
  intro z hz
  by_contra h
  apply hz
  refine ⟨(bosonPosition 0 z, bosonPosition 1 z), ?_, ?_⟩
  · exact ⟨subset_tsupport _ ((mul_ne_zero_iff.mp h).1),
      subset_tsupport _ ((mul_ne_zero_iff.mp h).2)⟩
  · ext ⟨i,j⟩
    fin_cases i <;> simp [bosonJoin]

private def productSchwartz {m : ℕ} (f g : SchwartzMap (WaveConfig m) ℂ)
    (hf : HasCompactSupport (f : WaveConfig m → ℂ))
    (hg : HasCompactSupport (g : WaveConfig m → ℂ)) : SchwartzMap (BosonConfig m) ℂ :=
  (compact_product f g hf hg).toSchwartzMap
    (((f.smooth ⊤).comp (contDiff_bosonPosition m 0)).mul
      ((g.smooth ⊤).comp (contDiff_bosonPosition m 1)))

private theorem productSchwartz_apply {m : ℕ} (f g : SchwartzMap (WaveConfig m) ℂ)
    (hf : HasCompactSupport (f : WaveConfig m → ℂ))
    (hg : HasCompactSupport (g : WaveConfig m → ℂ)) (z : BosonConfig m) :
    productSchwartz f g hf hg z = f (bosonPosition 0 z) * g (bosonPosition 1 z) := rfl

attribute [local irreducible] productSchwartz

private theorem productSchwartz_toLp {m : ℕ} (f g : SchwartzMap (WaveConfig m) ℂ)
    (hf : HasCompactSupport (f : WaveConfig m → ℂ))
    (hg : HasCompactSupport (g : WaveConfig m → ℂ)) :
    (productSchwartz f g hf hg).toLp 2 volume = waveTensor m (hilbertTmul (f.toLp 2 volume) (g.toLp 2 volume)) := by
  apply Lp.ext
  have h0 : QuasiMeasurePreserving (bosonPosition (m := m) 0) volume volume :=
    quasiMeasurePreserving_fst.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
  have h1 : QuasiMeasurePreserving (bosonPosition (m := m) 1) volume volume :=
    quasiMeasurePreserving_snd.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
  filter_upwards [(productSchwartz f g hf hg).coeFn_toLp 2 volume,
    waveTensor_tmul_coeFn m (f.toLp 2 volume) (g.toLp 2 volume),
    h0.ae_eq_comp (f.coeFn_toLp 2 volume), h1.ae_eq_comp (g.coeFn_toLp 2 volume)] with z hP hT hf' hg'
  simp only [Function.comp_apply] at hf' hg'
  rw [hP, hT, hf', hg', productSchwartz_apply]

private theorem inner_bosonPositions {m : ℕ} (z w : BosonConfig m) :
    inner ℝ z w = inner ℝ (bosonPosition 0 z) (bosonPosition 0 w) +
      inner ℝ (bosonPosition 1 z) (bosonPosition 1 w) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

private theorem fourier_productSchwartz {m : ℕ} (f g : SchwartzMap (WaveConfig m) ℂ)
    (hf : HasCompactSupport (f : WaveConfig m → ℂ))
    (hg : HasCompactSupport (g : WaveConfig m → ℂ)) (z : BosonConfig m) :
    (𝓕 (productSchwartz f g hf hg)) z =
      (𝓕 f) (bosonPosition 0 z) * (𝓕 g) (bosonPosition 1 z) := by
  change (𝓕 (productSchwartz f g hf hg : BosonConfig m → ℂ)) z =
    (𝓕 (f : WaveConfig m → ℂ)) (bosonPosition 0 z) *
      (𝓕 (g : WaveConfig m → ℂ)) (bosonPosition 1 z)
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_prod_mul]
  have hmeas : MeasurableEmbedding
      (fun z : BosonConfig m => (bosonPosition 0 z, bosonPosition 1 z)) :=
    (MeasurableEquiv.toLp 2 (WaveConfig m × WaveConfig m)).symm.measurableEmbedding.comp
      (splitConfigIsometry m).toMeasurableEquiv.measurableEmbedding
  rw [← (bosonPositions_measurePreserving m).integral_comp hmeas]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change (Real.fourierChar (-inner ℝ w z) : ℂ) * productSchwartz f g hf hg w = _
  rw [productSchwartz_apply, inner_bosonPositions, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  simp only [Circle.smul_def, smul_eq_mul]
  ring


private theorem waveFourier_schwartz (m : ℕ) (f : SchwartzMap (WaveConfig m) ℂ) :
    waveFourier m (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
  SchwartzMap.toLp_fourier_eq f

private theorem schrodingerFourier_schwartz (m : ℕ) (f : SchwartzMap (BosonConfig m) ℂ) :
    schrodingerFourier m (f.toLp 2 volume) = (𝓕 f).toLp 2 volume :=
  SchwartzMap.toLp_fourier_eq f

attribute [local irreducible] waveFourier schrodingerFourier

/-- The joint Fourier transform factors on product wavefunctions. -/
theorem schrodingerFourier_waveTensor_tmul (m : ℕ) (f g : WaveSpace m) :
    schrodingerFourier m (waveTensor m (hilbertTmul f g)) =
      waveTensor m (hilbertTmul (waveFourier m f) (waveFourier m g)) := by
  refine (dense_compactSchwartz m).induction_on₂
    (p := fun f g : WaveSpace m => schrodingerFourier m (waveTensor m (hilbertTmul f g)) =
      waveTensor m (hilbertTmul (waveFourier m f) (waveFourier m g))) ?_ ?_ f g
  · apply isClosed_eq
    · exact (schrodingerFourier m).continuous.comp
        ((waveTensor m).continuous.comp hilbertTmul.continuous₂)
    · have h₁ : Continuous (fun p : WaveSpace m × WaveSpace m =>
          (hilbertTmul (E := WaveSpace m) (F := WaveSpace m)) (waveFourier m p.1)) :=
        hilbertTmul.continuous.comp ((waveFourier m).continuous.comp continuous_fst)
      have h₂ : Continuous (fun p : WaveSpace m × WaveSpace m => waveFourier m p.2) :=
        (waveFourier m).continuous.comp continuous_snd
      exact (waveTensor m).continuous.comp (h₁.clm_apply h₂)
  intro f g
  rw [← productSchwartz_toLp f.val g.val f.property g.property]
  have hleft := schrodingerFourier_schwartz m (productSchwartz f.val g.val f.property g.property)
  have hright := congrArg₂ (fun a b : WaveSpace m => waveTensor m (hilbertTmul a b))
    (waveFourier_schwartz m f.val) (waveFourier_schwartz m g.val)
  apply hleft.trans
  apply Eq.trans _ hright.symm
  apply Lp.ext
  have h0 : QuasiMeasurePreserving (bosonPosition (m := m) 0) volume volume :=
    quasiMeasurePreserving_fst.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
  have h1 : QuasiMeasurePreserving (bosonPosition (m := m) 1) volume volume :=
    quasiMeasurePreserving_snd.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
  filter_upwards [(𝓕 (productSchwartz f.val g.val f.property g.property)).coeFn_toLp 2 volume,
    waveTensor_tmul_coeFn m ((𝓕 f.val).toLp 2 volume) ((𝓕 g.val).toLp 2 volume),
    h0.ae_eq_comp ((𝓕 f.val).coeFn_toLp 2 volume), h1.ae_eq_comp ((𝓕 g.val).coeFn_toLp 2 volume)]
    with z hP hT hf hg
  simp only [Function.comp_apply] at hf hg
  rw [hP, hT, hf, hg, fourier_productSchwartz]

/-- The canonical wavefunction identification intertwines the tensor Fourier
unitary with the Fourier transform on the joint configuration. -/
theorem schrodingerFourier_waveTensor (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    schrodingerFourier m (waveTensor m v) = waveTensor m (hilbertTensorMap
      (waveFourier m).toLinearIsometry.toContinuousLinearMap
      (waveFourier m).toLinearIsometry.toContinuousLinearMap v) := by
  have h : (schrodingerFourier m).toLinearIsometry.toContinuousLinearMap.comp
      (waveTensor m).toContinuousLinearMap =
    (waveTensor m).toContinuousLinearMap.comp (hilbertTensorMap
      (waveFourier m).toLinearIsometry.toContinuousLinearMap
      (waveFourier m).toLinearIsometry.toContinuousLinearMap) := by
    apply hilbertTensor_ext
    intro f g
    simp only [ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    exact schrodingerFourier_waveTensor_tmul m f g
  exact congrArg (fun B => B v) h

/-- Applying the same Fourier Gaussian unitary to both copies commutes exactly
with every copy rotation. -/
theorem schrodingerTensorRotation_fourier (m : ℕ) (θ : ℝ)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorRotation m θ (hilbertTensorMap
      (waveFourier m).toLinearIsometry.toContinuousLinearMap
      (waveFourier m).toLinearIsometry.toContinuousLinearMap v) =
    hilbertTensorMap (waveFourier m).toLinearIsometry.toContinuousLinearMap
      (waveFourier m).toLinearIsometry.toContinuousLinearMap
      (schrodingerTensorRotation m θ v) := by
  apply (waveTensorEquiv m).injective
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, waveTensorEquiv_apply]
  rw [← schrodingerFourier_waveTensor, ← schrodingerFourier_waveTensor]
  simp only [← waveTensorEquiv_apply, LinearIsometryEquiv.apply_symm_apply]
  exact (schrodingerFourier_rotation m θ _).symm

end
end GaussianTesting
