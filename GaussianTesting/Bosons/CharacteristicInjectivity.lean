module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PureCharacteristic
public import GaussianTesting.Bosons.FourierUniqueness
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public section

/-!
# Recovering pure states from their characteristic functions

For each fixed position displacement, the Weyl characteristic function is the
Fourier transform of an integrable cross-correlation. Fourier uniqueness and
Fubini recover the rank-one kernel and therefore the pure-state density operator.
-/

namespace GaussianTesting

open MeasureTheory FourierTransform
open scoped InnerProductSpace

noncomputable section

/-- The integrable correlation associated with a fixed position displacement. -/
def waveCorrelation {m : ℕ} (f : WaveSpace m) (q x : WaveConfig m) : ℂ :=
  inner ℂ (f x) (f (x-q))

theorem integrable_waveCorrelation {m : ℕ} (f : WaveSpace m) (q : WaveConfig m) :
    Integrable (waveCorrelation f q) := by
  apply (L2.integrable_inner f (waveTranslation m q f)).congr
  filter_upwards [waveTranslation_coeFn m q f] with x hx
  simp only [waveCorrelation, hx]

/-- The frequency slice of a pure-state characteristic function is the Fourier
transform of its correlation, with the phase fixed by the Weyl convention. -/
theorem pureWaveCharacteristic_fourier {m : ℕ} (f : WaveSpace m)
    (q t : WaveConfig m) :
    pureWaveCharacteristic m f (q, (-2 * Real.pi) • t) =
      Complex.exp (-Complex.I * (inner ℝ ((-2 * Real.pi) • t) q : ℂ) / 2) *
        𝓕 (waveCorrelation f q) t := by
  rw [pureWaveCharacteristic, weylOperator_factorization, inner_smul_right]
  congr 1
  rw [L2.inner_def, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [waveModulation_coeFn m ((-2 * Real.pi) • t) (waveTranslation m q f),
    waveTranslation_coeFn m q f] with x hm ht
  rw [hm, ht]
  have he : Complex.exp (Complex.I * (inner ℝ ((-2 * Real.pi) • t) x : ℂ)) =
      Complex.exp (((-2 * Real.pi * inner ℝ x t : ℝ) : ℂ) * Complex.I) := by
    congr 1
    simp only [real_inner_smul_left, real_inner_comm t x]
    push_cast
    ring
  simp only [waveCorrelation, RCLike.inner_apply, smul_eq_mul, he]
  ring

/-- Equal characteristic functions give equal position correlations almost
everywhere for every displacement. -/
theorem waveCorrelation_eq_of_characteristic_eq {m : ℕ} (f g : WaveSpace m)
    (h : pureWaveCharacteristic m f = pureWaveCharacteristic m g) (q : WaveConfig m) :
    waveCorrelation f q =ᵐ[volume] waveCorrelation g q := by
  apply ae_eq_of_fourier_eq (integrable_waveCorrelation f q) (integrable_waveCorrelation g q)
  intro t
  have hq := congrFun h (q, (-2 * Real.pi) • t)
  rw [pureWaveCharacteristic_fourier, pureWaveCharacteristic_fourier] at hq
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hq

/-- Equal pure-state characteristic functions determine the rank-one kernels
almost everywhere on the product configuration space. -/
theorem wavePureKernel_eq_of_characteristic_eq {m : ℕ} (f g : WaveSpace m)
    (h : pureWaveCharacteristic m f = pureWaveCharacteristic m g) :
    (fun z : WaveConfig m × WaveConfig m => inner ℂ (f z.1) (f z.2))
      =ᵐ[volume.prod volume]
    (fun z : WaveConfig m × WaveConfig m => inner ℂ (g z.1) (g z.2)) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  have hprod :
      (fun z : WaveConfig m × WaveConfig m => inner ℂ (f z.2) (f (z.2+z.1)))
        =ᵐ[volume.prod volume]
      (fun z : WaveConfig m × WaveConfig m => inner ℂ (g z.2) (g (z.2+z.1))) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((hf.comp measurable_snd).inner (hf.comp (measurable_snd.add measurable_fst)))
      ((hg.comp measurable_snd).inner (hg.comp (measurable_snd.add measurable_fst))))).mpr
    exact Filter.Eventually.of_forall fun q => by
      simpa only [Filter.EventuallyEq, waveCorrelation, sub_neg_eq_add, Function.comp_apply, Pi.add_apply] using
        waveCorrelation_eq_of_characteristic_eq f g h (-q)
  have hchange : MeasurePreserving
      (fun z : WaveConfig m × WaveConfig m => (z.2-z.1,z.1))
      (volume.prod volume) (volume.prod volume) :=
    Measure.measurePreserving_swap.comp (measurePreserving_prod_sub volume volume)
  filter_upwards [hchange.quasiMeasurePreserving.ae hprod] with z hz
  change inner ℂ (f z.1) (f (z.1+(z.2-z.1))) =
    inner ℂ (g z.1) (g (z.1+(z.2-z.1))) at hz
  simpa only [show z.1+(z.2-z.1)=z.2 by abel] using hz

/-- A pure state's characteristic function determines its density operator.
There are no continuity, moment, or nonzero-vector assumptions. -/
theorem rankOne_eq_of_pureWaveCharacteristic_eq {m : ℕ} (f g : WaveSpace m)
    (h : pureWaveCharacteristic m f = pureWaveCharacteristic m g) :
    InnerProductSpace.rankOne ℂ f f = InnerProductSpace.rankOne ℂ g g := by
  have hk := wavePureKernel_eq_of_characteristic_eq f g h
  ext v : 1
  apply ext_inner_left ℂ
  intro u
  simp only [InnerProductSpace.rankOne_apply, inner_smul_right]
  rw [L2.inner_def, L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_prod_mul, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [hk] with z hz
  simp only [RCLike.inner_apply, starRingEnd_apply] at hz ⊢
  calc
    _ = (f z.2 * star (f z.1)) * (v z.1 * star (u z.2)) := by ring
    _ = (g z.2 * star (g z.1)) * (v z.1 * star (u z.2)) := by rw [hz]
    _ = _ := by ring

end
end GaussianTesting
