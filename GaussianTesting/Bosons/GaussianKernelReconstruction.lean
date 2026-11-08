module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.CharacteristicInjectivity
public import GaussianTesting.Bosons.WaveGaussian
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Reconstructing a centered Gaussian wavefunction from its correlations

Fourier slices determine the correlations almost everywhere. A nonzero slice
gives a continuous Gaussian representative. Continuity then promotes the
rank-one kernel identity to every pair of positions, allowing evaluation at
the origin without choosing an exceptional-value representative of `L²`.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-- Continuous nonvanishing Gaussian correlations supply a continuous
representative with the same kernel identity at every pair of positions. -/
theorem continuous_representative_of_gaussian_correlation {m : ℕ} (f : WaveSpace m)
    (R : WavePhase m → ℂ) (hR : Continuous R) (C : ℂ) (hC : C ≠ 0)
    (hcorr : ∀ q, waveCorrelation f q =ᵐ[volume] fun x => C * Complex.exp (R (q,x))) :
    ∃ g : WaveConfig m → ℂ, Continuous g ∧ f =ᵐ[volume] g ∧
      (∀ x, g x ≠ 0) ∧
      ∀ x y, inner ℂ (g x) (g y) = C * Complex.exp (R (x-y,x)) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hprod :
      (fun z : WaveConfig m × WaveConfig m => inner ℂ (f z.2) (f (z.2+z.1)))
        =ᵐ[volume.prod volume]
      (fun z => C * Complex.exp (R (-z.1,z.2))) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((hf.comp measurable_snd).inner (hf.comp (measurable_snd.add measurable_fst)))
      (by fun_prop))).mpr
    exact Filter.Eventually.of_forall fun q => by
      simpa only [Filter.EventuallyEq, waveCorrelation, sub_neg_eq_add, Function.comp_apply, Pi.add_apply] using hcorr (-q)
  have hchange : MeasurePreserving
      (fun z : WaveConfig m × WaveConfig m => (z.2-z.1,z.1))
      (volume.prod volume) (volume.prod volume) :=
    Measure.measurePreserving_swap.comp (measurePreserving_prod_sub volume volume)
  have hk :
      (fun z : WaveConfig m × WaveConfig m => inner ℂ (f z.1) (f z.2))
        =ᵐ[volume.prod volume]
      (fun z => C * Complex.exp (R (z.1-z.2,z.1))) := by
    filter_upwards [hchange.quasiMeasurePreserving.ae hprod] with z hz
    simpa only [show z.1 + (z.2-z.1) = z.2 by abel,
      show -(z.2-z.1) = z.1-z.2 by abel] using hz
  have hnonzero : ∀ᵐ x ∂volume, f x ≠ 0 := by
    filter_upwards [hcorr 0] with x hx
    intro hz
    simp only [waveCorrelation, sub_zero, hz, inner_zero_left] at hx
    exact (mul_ne_zero hC (Complex.exp_ne_zero _)) hx.symm
  obtain ⟨x₀, hx₀, hk₀⟩ := (hnonzero.and (Measure.ae_ae_of_ae_prod hk)).exists
  let g (y : WaveConfig m) := (star (f x₀))⁻¹ * C * Complex.exp (R (x₀-y,x₀))
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hk₀] with y hy
    rw [RCLike.inner_apply, mul_comm] at hy
    dsimp [g]
    rw [mul_assoc, ← hy]
    exact (inv_mul_cancel_left₀ (show (starRingEnd ℂ) (f x₀) ≠ 0 from star_ne_zero.mpr hx₀) _).symm
  have hk' :
      (fun z : WaveConfig m × WaveConfig m => inner ℂ (g z.1) (g z.2)) =
      (fun z => C * Complex.exp (R (z.1-z.2,z.1))) := by
    apply Measure.eq_of_ae_eq (μ := volume.prod volume) _ (by fun_prop) (by fun_prop)
    filter_upwards [hk, Measure.quasiMeasurePreserving_fst.ae hfg,
      Measure.quasiMeasurePreserving_snd.ae hfg] with z hz hx hy
    rwa [hx, hy] at hz
  refine ⟨g, hg, hfg, ?_, fun x y => congrFun hk' (x,y)⟩
  intro x
  dsimp [g]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (star_ne_zero.mpr hx₀)) hC)
    (Complex.exp_ne_zero _)

/-- A homogeneous quadratic correlation kernel reconstructs a homogeneous
quadratic wavefunction, with equality in the actual `L²` sense. -/
theorem wavefunction_of_gaussian_correlation {m : ℕ} (f : WaveSpace m)
    (R : QuadraticMap ℝ (WavePhase m) ℂ) (hR : Continuous R) (C : ℂ) (hC : C ≠ 0)
    (hcorr : ∀ q, waveCorrelation f q =ᵐ[volume] fun x => C * Complex.exp (R (q,x))) :
    ∃ c : ℂ, c ≠ 0 ∧ f =ᵐ[volume] fun x => c * Complex.exp (R (-x,0)) := by
  obtain ⟨g, _, hfg, hgn, hk⟩ := continuous_representative_of_gaussian_correlation f R hR C hC hcorr
  let c := (star (g 0))⁻¹ * C
  refine ⟨c, mul_ne_zero (inv_ne_zero (star_ne_zero.mpr (hgn 0))) hC, ?_⟩
  filter_upwards [hfg] with x hx
  rw [hx]
  have h := hk 0 x
  rw [RCLike.inner_apply, mul_comm] at h
  simp only [zero_sub] at h
  dsimp [c]
  rw [mul_assoc, ← h]
  exact (inv_mul_cancel_left₀ (show (starRingEnd ℂ) (g 0) ≠ 0 from star_ne_zero.mpr (hgn 0)) _).symm

end
end GaussianTesting
