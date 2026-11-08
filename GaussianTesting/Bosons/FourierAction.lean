module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.LinearChange
public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public section

/-!
# Fourier Gaussian unitary on Schrödinger wavefunctions

We use Mathlib's unitary Fourier transform, with kernel `exp(-2πi⟪x,ξ⟫)`.
The corresponding symplectic parameter change includes the explicit factors
`2π`; no change of Fourier normalization is implicit.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace FourierTransform

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

/-- The unitary Fourier transform with Mathlib's `2π` normalization. -/
def waveFourier (m : ℕ) : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m :=
  Lp.fourierTransformₗᵢ (WaveConfig m) ℂ

private theorem translation_schwartz_toLp (m : ℕ) (q : WaveConfig m)
    (f : SchwartzMap (WaveConfig m) ℂ) :
    waveTranslation m q (f.toLp 2) = (f.compSubConstCLM ℂ q).toLp 2 := by
  apply Lp.ext
  filter_upwards [waveTranslation_coeFn m q (f.toLp 2),
    (waveTranslation_measurePreserving q).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2),
    (f.compSubConstCLM ℂ q).coeFn_toLp 2] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃, SchwartzMap.compSubConstCLM_apply]

private theorem phase_temperate {m : ℕ} (p : WaveConfig m) :
    (fun x : WaveConfig m => Complex.exp (Complex.I * (inner ℝ p x : ℂ))).HasTemperateGrowth := by
  have h : (fun x : WaveConfig m => Complex.exp ((inner ℝ p x : ℂ) * Complex.I)).HasTemperateGrowth := by
    exact Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ p).hasTemperateGrowth
  simpa only [mul_comm] using h

private def schwartzModulation {m : ℕ} (p : WaveConfig m)
    (f : SchwartzMap (WaveConfig m) ℂ) : SchwartzMap (WaveConfig m) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (Complex.I * (inner ℝ p x : ℂ))) f

private theorem schwartzModulation_apply {m : ℕ} (p : WaveConfig m)
    (f : SchwartzMap (WaveConfig m) ℂ) (x : WaveConfig m) :
    schwartzModulation p f x = Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * f x := by
  simp only [schwartzModulation, SchwartzMap.smulLeftCLM_apply_apply (phase_temperate p),
    smul_eq_mul]

private theorem modulation_schwartz_toLp (m : ℕ) (p : WaveConfig m)
    (f : SchwartzMap (WaveConfig m) ℂ) :
    waveModulation m p (f.toLp 2) = (schwartzModulation p f).toLp 2 := by
  apply Lp.ext
  filter_upwards [waveModulation_coeFn m p (f.toLp 2), f.coeFn_toLp 2,
    (schwartzModulation p f).coeFn_toLp 2] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, schwartzModulation_apply]

private theorem fourier_translation_schwartz (m : ℕ) (q : WaveConfig m)
    (f : SchwartzMap (WaveConfig m) ℂ) (x : WaveConfig m) :
    (𝓕 (f.compSubConstCLM ℂ q)) x =
      Complex.exp (Complex.I * (inner ℝ (- (2 * Real.pi) • q) x : ℂ)) * (𝓕 f) x := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ (WaveConfig m)) (f : WaveConfig m → ℂ) (-q)) x
  change (𝓕 ((f : WaveConfig m → ℂ) ∘ fun y => y + -q)) x = _ at h
  change (𝓕 ((f : WaveConfig m → ℂ) ∘ fun y => y - q)) x = _
  simp only [sub_eq_add_neg]
  rw [h]
  simp only [Circle.smul_def, Real.fourierChar_apply, innerₗ_apply_apply, inner_neg_left,
    real_inner_smul_left, smul_eq_mul]
  congr 2
  push_cast
  ring

private theorem fourier_modulation_schwartz (m : ℕ) (p : WaveConfig m)
    (f : SchwartzMap (WaveConfig m) ℂ) (x : WaveConfig m) :
    (𝓕 (schwartzModulation p f)) x = (𝓕 f) (x - (2 * Real.pi)⁻¹ • p) := by
  change (𝓕 (schwartzModulation p f : WaveConfig m → ℂ)) x =
    (𝓕 (f : WaveConfig m → ℂ)) (x - (2 * Real.pi)⁻¹ • p)
  rw [Real.fourier_eq', Real.fourier_eq']
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change Complex.exp _ • schwartzModulation p f y = Complex.exp _ • f y
  rw [schwartzModulation_apply]
  simp only [smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  rw [inner_sub_right, inner_smul_right, real_inner_comm y p]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Fourier transform exchanges position translations and momentum modulations. -/
theorem waveFourier_translation (m : ℕ) (q : WaveConfig m) (f : WaveSpace m) :
    waveFourier m (waveTranslation m q f) =
      waveModulation m (-(2 * Real.pi) • q) (waveFourier m f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := WaveConfig m) (F := ℂ)
    (p := 2) (μ := volume) ENNReal.ofNat_ne_top).induction_on
    (p := fun f : WaveSpace m => waveFourier m (waveTranslation m q f) =
      waveModulation m (-(2 * Real.pi) • q) (waveFourier m f)) f ?_ ?_
  · exact isClosed_eq ((waveFourier m).continuous.comp (waveTranslation m q).continuous)
      ((waveModulation m _).continuous.comp (waveFourier m).continuous)
  intro g
  change waveFourier m (waveTranslation m q (g.toLp 2)) =
    waveModulation m _ (waveFourier m (g.toLp 2))
  rw [translation_schwartz_toLp]
  change 𝓕 ((g.compSubConstCLM ℂ q).toLp 2) = waveModulation m _ (𝓕 (g.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (g.compSubConstCLM ℂ q)).coeFn_toLp 2,
    waveModulation_coeFn m (-(2 * Real.pi) • q) ((𝓕 g).toLp 2),
    (𝓕 g).coeFn_toLp 2] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, fourier_translation_schwartz]

/-- Fourier transform exchanges momentum modulations and position translations. -/
theorem waveFourier_modulation (m : ℕ) (p : WaveConfig m) (f : WaveSpace m) :
    waveFourier m (waveModulation m p f) =
      waveTranslation m ((2 * Real.pi)⁻¹ • p) (waveFourier m f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := WaveConfig m) (F := ℂ)
    (p := 2) (μ := volume) ENNReal.ofNat_ne_top).induction_on
    (p := fun f : WaveSpace m => waveFourier m (waveModulation m p f) =
      waveTranslation m ((2 * Real.pi)⁻¹ • p) (waveFourier m f)) f ?_ ?_
  · exact isClosed_eq ((waveFourier m).continuous.comp (waveModulation m p).continuous)
      ((waveTranslation m _).continuous.comp (waveFourier m).continuous)
  intro g
  change waveFourier m (waveModulation m p (g.toLp 2)) =
    waveTranslation m _ (waveFourier m (g.toLp 2))
  rw [modulation_schwartz_toLp]
  change 𝓕 ((schwartzModulation p g).toLp 2) = waveTranslation m _ (𝓕 (g.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (schwartzModulation p g)).coeFn_toLp 2,
    waveTranslation_coeFn m ((2 * Real.pi)⁻¹ • p) ((𝓕 g).toLp 2),
    (waveTranslation_measurePreserving ((2 * Real.pi)⁻¹ • p)).quasiMeasurePreserving.ae_eq_comp
      ((𝓕 g).coeFn_toLp 2)] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃, fourier_modulation_schwartz]


/-- The symplectic parameter map for conjugation by the Fourier transform. -/
def waveFourierPhase {m : ℕ} (r : WavePhase m) : WavePhase m :=
  ((2 * Real.pi)⁻¹ • r.2, -(2 * Real.pi) • r.1)

/-- Exact Weyl covariance for the Fourier Gaussian unitary. -/
theorem waveFourier_weyl (m : ℕ) (r : WavePhase m) (f : WaveSpace m) :
    waveFourier m (weylOperator m r f) =
      weylOperator m (waveFourierPhase r) (waveFourier m f) := by
  rw [weylOperator_factorization, map_smul, waveFourier_modulation, waveFourier_translation]
  apply Lp.ext
  let c : ℂ := Complex.exp (-Complex.I * (inner ℝ r.2 r.1 : ℂ) / 2)
  let q := (2 * Real.pi)⁻¹ • r.2
  let p := -(2 * Real.pi) • r.1
  filter_upwards [Lp.coeFn_smul c (waveTranslation m q (waveModulation m p (waveFourier m f))),
    waveTranslation_coeFn m q (waveModulation m p (waveFourier m f)),
    (waveTranslation_measurePreserving q).quasiMeasurePreserving.ae_eq_comp
      (waveModulation_coeFn m p (waveFourier m f)),
    weylOperator_coeFn m (waveFourierPhase r) (waveFourier m f)] with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₄]
  simp only [Pi.smul_apply, smul_eq_mul, h₂, h₃]
  change c * (Complex.exp (Complex.I * (inner ℝ p (x-q) : ℂ)) * _) =
    weylPhase (q,p) x * _
  rw [← mul_assoc]
  congr 1
  dsimp [c, weylPhase, p, q]
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_sub_right, real_inner_smul_left, inner_smul_right]
  rw [real_inner_comm r.1 r.2]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Fourier conjugation preserves the symplectic form despite the `2π`
normalization of the transform. -/
theorem waveFourierPhase_symplectic {m : ℕ} (r s : WavePhase m) :
    waveSymplectic (waveFourierPhase r) (waveFourierPhase s) = waveSymplectic r s := by
  simp only [waveSymplectic, waveFourierPhase, real_inner_smul_left, inner_smul_right]
  field_simp
  ring


/-- Fourier covariance in the manuscript's `U† D_r U` convention. -/
theorem waveFourier_conjugate (m : ℕ) (r : WavePhase m) (f : WaveSpace m) :
    (waveFourier m).symm (weylOperator m r (waveFourier m f)) =
      weylOperator m (-(2 * Real.pi)⁻¹ • r.2, (2 * Real.pi) • r.1) f := by
  apply (waveFourier m).injective
  rw [LinearIsometryEquiv.apply_symm_apply, waveFourier_weyl]
  have h : waveFourierPhase (-(2 * Real.pi)⁻¹ • r.2, (2 * Real.pi) • r.1) = r := by
    apply Prod.ext
    · change (2 * Real.pi)⁻¹ • ((2 * Real.pi) • r.1) = r.1
      rw [smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
    · change -(2 * Real.pi) • (-(2 * Real.pi)⁻¹ • r.2) = r.2
      rw [smul_smul, neg_mul_neg, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  rw [h]

end
end GaussianTesting
