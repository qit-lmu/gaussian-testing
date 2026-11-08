module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Weyl

@[expose] public section

/-!
# Strong continuity of Weyl displacements

Translation is continuous in the `L²` norm. Modulation is strongly continuous
by dominated convergence, with the squared difference bounded by `4 |f|²`.
These facts give continuity of the explicit Weyl action in both its phase-space
parameter and the input wavefunction; operator-norm continuity is not asserted.
-/

namespace GaussianTesting

open MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

private theorem wave_norm_sq_integral {m : ℕ} (f : WaveSpace m) :
    ‖f‖ ^ 2 = ∫ x : WaveConfig m, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm

private theorem continuous_modulation_of_coeFn (m : ℕ)
    (M : WaveConfig m → WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m)
    (hM : ∀ p f, (M p f : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * f x)
    (f : WaveSpace m) : Continuous fun p => M p f := by
  let phase (p x : WaveConfig m) : ℂ := Complex.exp (Complex.I * (inner ℝ p x : ℂ))
  have hphase (p : WaveConfig m) : Continuous (phase p) := by
    dsimp [phase]
    fun_prop
  have hphase' (x : WaveConfig m) : Continuous fun p => phase p x := by
    dsimp [phase]
    fun_prop
  have hn (p x : WaveConfig m) : ‖phase p x‖ = 1 :=
    Complex.norm_exp_I_mul_ofReal _
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let F (p x : WaveConfig m) : ℝ := ‖(phase p x - phase p₀ x) * f x‖ ^ 2
  have hmeas (p : WaveConfig m) : AEStronglyMeasurable (F p) volume :=
    ((((hphase p).aestronglyMeasurable.sub (hphase p₀).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)).norm).pow 2
  have hbound (p : WaveConfig m) : ∀ᵐ x ∂volume, ‖F p x‖ ≤ 4 * ‖f x‖ ^ 2 := by
    apply Filter.Eventually.of_forall
    intro x
    have hb : ‖phase p x - phase p₀ x‖ ≤ 2 := by
      simpa only [hn, one_add_one_eq_two] using norm_sub_le (phase p x) (phase p₀ x)
    dsimp [F]
    rw [abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have hs : ‖phase p x - phase p₀ x‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (phase p x - phase p₀ x)]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hdom : Integrable (fun x : WaveConfig m => 4 * ‖f x‖ ^ 2) volume :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)).const_mul 4
  have hc : Continuous (fun p => ∫ x, F p x) :=
    continuous_of_dominated hmeas hbound hdom (Filter.Eventually.of_forall fun x =>
      (((hphase' x).sub continuous_const).mul continuous_const).norm.pow 2)
  have heq (p : WaveConfig m) : ‖M p f - M p₀ f‖ ^ 2 = ∫ x, F p x := by
    rw [wave_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (M p f) (M p₀ f), hM p f, hM p₀ f] with x hx hp hp₀
    rw [hx, Pi.sub_apply, hp, hp₀]
    dsimp [F, phase]
    rw [sub_mul]
  have hs : Tendsto (fun p => Real.sqrt (∫ x, F p x)) (𝓝 p₀)
      (𝓝 (Real.sqrt (∫ x, F p₀ x))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hc.continuousAt.tendsto
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [← heq, Real.sqrt_sq_eq_abs, abs_norm, sub_self, norm_zero, abs_zero] using hs

private theorem continuous_translation_of_coeFn (m : ℕ)
    (T : WaveConfig m → WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m)
    (hT : ∀ q f, (T q f : WaveConfig m → ℂ) =ᵐ[volume] fun x => f (x - q))
    (f : WaveSpace m) : Continuous fun q => T q f := by
  let shift (q : WaveConfig m) : C(WaveConfig m, WaveConfig m) :=
    ⟨fun x => x - q, continuous_id.sub continuous_const⟩
  have hs : Continuous shift :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)
  have hm (q : WaveConfig m) : MeasurePreserving (shift q) volume volume :=
    measurePreserving_sub_right volume q
  have heq (q : WaveConfig m) :
      T q f = Lp.compMeasurePreserving (shift q) (hm q) f := by
    apply Lp.ext
    exact (hT q f).trans (Lp.coeFn_compMeasurePreserving f (hm q)).symm
  simp_rw [heq]
  exact continuous_const.compMeasurePreservingLp hs hm (by norm_num)

/-- Strong continuity of translations in the position parameter. -/
theorem continuous_waveTranslation (m : ℕ) (f : WaveSpace m) :
    Continuous fun q => waveTranslation m q f :=
  continuous_translation_of_coeFn m (waveTranslation m) (waveTranslation_coeFn m) f

/-- Translation is jointly continuous in the position parameter and input. -/
theorem continuous_waveTranslation_apply (m : ℕ) :
    Continuous (fun p : WaveConfig m × WaveSpace m => waveTranslation m p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun q => (waveTranslation m q).isometry.lipschitzWith)
    (continuous_waveTranslation m)

/-- Strong continuity of modulation in the momentum parameter. -/
theorem continuous_waveModulation (m : ℕ) (f : WaveSpace m) :
    Continuous fun p => waveModulation m p f :=
  continuous_modulation_of_coeFn m (waveModulation m) (waveModulation_coeFn m) f

/-- Modulation is jointly continuous in the momentum parameter and input. -/
theorem continuous_waveModulation_apply (m : ℕ) :
    Continuous (fun p : WaveConfig m × WaveSpace m => waveModulation m p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun p => (waveModulation m p).isometry.lipschitzWith)
    (continuous_waveModulation m)

-- Use the checked factorization without unfolding the underlying `Lp` constructions.
attribute [local irreducible] waveModulation waveTranslation weylOperator

/-- Weyl displacements are strongly continuous on the actual Schrödinger space. -/
theorem continuous_weylOperator (m : ℕ) (f : WaveSpace m) :
    Continuous (fun r : WavePhase m => weylOperator m r f) := by
  have hphase : Continuous (fun r : WavePhase m =>
      Complex.exp (-Complex.I * (inner ℝ r.2 r.1 : ℂ) / 2)) := by fun_prop
  have ht : Continuous (fun r : WavePhase m => waveTranslation m r.1 f) :=
    (continuous_waveTranslation m f).comp continuous_fst
  have hm : Continuous (fun r : WavePhase m =>
      waveModulation m r.2 (waveTranslation m r.1 f)) :=
    (continuous_waveModulation_apply m).comp (continuous_snd.prodMk ht)
  have h : Continuous (fun r : WavePhase m =>
      Complex.exp (-Complex.I * (inner ℝ r.2 r.1 : ℂ) / 2) •
        waveModulation m r.2 (waveTranslation m r.1 f)) := hphase.smul hm
  exact h.congr (fun r => (weylOperator_factorization m r f).symm)

/-- The displacement action is jointly continuous in phase space and the input
wavefunction, for their usual Euclidean and `L²` norm topologies. -/
theorem continuous_weylOperator_apply (m : ℕ) :
    Continuous (fun p : WavePhase m × WaveSpace m => weylOperator m p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun r => (weylOperator m r).isometry.lipschitzWith)
    (continuous_weylOperator m)

end
end GaussianTesting
