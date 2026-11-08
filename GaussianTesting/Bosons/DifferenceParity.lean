module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerSwap
public import GaussianTesting.Bosons.FourierAction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Even parity of the difference output

The assertion following Theorem 1.1 concerns identical pure inputs. Input
swap becomes parity on the difference register after the inverse balanced
rotation. Thus every column of the output, and the range of its reduced
density operator, lies in the even subspace.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open FourierTransform
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The inverse balanced splitter sends identical inputs to a vector with
even parity on its difference register. -/
theorem schrodingerDifference_even (m : ℕ) (ψ : WaveSpace m) :
    hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
      (waveParity m).toLinearIsometry.toContinuousLinearMap
      ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) =
    (schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ) := by
  have h := schrodingerTensorRotation_balanced_swap m
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ))
  have hU := (schrodingerTensorRotation m (Real.pi / 4)).apply_symm_apply
    (hilbertTmul ψ ψ)
  have hS := congrArg hilbertSwap hU
  exact (schrodingerTensorRotation m (Real.pi / 4)).injective
    (((h.symm.trans hS).trans (hilbertSwap_tmul ψ ψ)).trans hU.symm)

/-- Each vector in the canonical Gram representation of the difference
output is even. This is stronger than invariance of the density operator
under conjugation by parity. -/
theorem schrodingerDifference_column_even {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (i : κ) :
    waveParity m (HilbertDensity.rightColumn b b
      ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i) =
    HilbertDensity.rightColumn b b
      ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i := by
  have h := congrArg (fun Φ => HilbertDensity.rightColumn b b Φ i)
    (schrodingerDifference_even m ψ)
  simpa only [HilbertDensity.rightColumn_tensorMap,
    LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry] using h

/-- The reduced difference state is supported on the even-parity subspace. -/
theorem schrodingerReducedState_even {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ f : WaveSpace m) :
    waveParity m (schrodingerReducedState b ψ f) = schrodingerReducedState b ψ f := by
  let Φ := (schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)
  have hs := HilbertDensity.gramOp_hasSum b
    (HilbertDensity.rightColumn_gramFam b b Φ) f
  have ht := hs.mapL (waveParity m).toLinearIsometry.toContinuousLinearMap
  have he : (fun i => waveParity m
      (inner ℂ (HilbertDensity.rightColumn b b Φ i) f •
        HilbertDensity.rightColumn b b Φ i)) =
      (fun i => inner ℂ (HilbertDensity.rightColumn b b Φ i) f •
        HilbertDensity.rightColumn b b Φ i) := by
    funext i
    rw [map_smul, schrodingerDifference_column_even]
  change HasSum (fun i => waveParity m
    (inner ℂ (HilbertDensity.rightColumn b b Φ i) f •
      HilbertDensity.rightColumn b b Φ i)) (waveParity m (schrodingerReducedState b ψ f)) at ht
  rw [he] at ht
  exact ht.unique hs

/-- Every integrable odd position observable has zero expectation in an
even wavefunction. The integrability hypothesis states existence of the
moment, as in the manuscript. -/
theorem integral_odd_of_waveParity_eq_self {m : ℕ} {f : WaveSpace m}
    (hf : waveParity m f = f) (a : WaveConfig m → ℝ)
    (ha : ∀ x, a (-x) = -a x)
    (_hint : Integrable (fun x => a x * ‖f x‖ ^ 2) volume) :
    ∫ x, a x * ‖f x‖ ^ 2 = 0 := by
  have he : (fun x => f (-x)) =ᵐ[volume] f := by
    simpa only [hf] using (waveParity_coeFn m f).symm
  have hneg : (∫ x, a (-x) * ‖f (-x)‖ ^ 2) = ∫ x, a x * ‖f x‖ ^ 2 :=
    integral_neg_eq_self (fun x : WaveConfig m => a x * ‖f x‖ ^ 2) volume
  have hodd : (∫ x, a (-x) * ‖f (-x)‖ ^ 2) = -(∫ x, a x * ‖f x‖ ^ 2) := by
    calc
      _ = ∫ x, -(a x * ‖f x‖ ^ 2) := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [ha, hx, neg_mul]
      _ = _ := integral_neg _
  linarith

private theorem waveParity_fourier_eq_inverse (m : ℕ) (f : WaveSpace m) :
    waveParity m (waveFourier m f) = (waveFourier m).symm f := by
  refine (SchwartzMap.denseRange_toLpCLM (E := WaveConfig m) (F := ℂ)
    (p := 2) (μ := volume) ENNReal.ofNat_ne_top).induction_on
    (p := fun f : WaveSpace m => waveParity m (waveFourier m f) =
      (waveFourier m).symm f) f ?_ ?_
  · exact isClosed_eq ((waveParity m).continuous.comp (waveFourier m).continuous)
      (waveFourier m).symm.continuous
  intro g
  change waveParity m (𝓕 (g.toLp 2)) = 𝓕⁻ (g.toLp 2)
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourierInv_eq]
  apply Lp.ext
  have hn : MeasurePreserving (fun x : WaveConfig m => -x) :=
    (LinearIsometryEquiv.neg ℝ : WaveConfig m ≃ₗᵢ[ℝ] WaveConfig m).measurePreserving
  filter_upwards [waveParity_coeFn m ((𝓕 g).toLp 2),
    hn.quasiMeasurePreserving.ae_eq_comp ((𝓕 g).coeFn_toLp 2),
    (𝓕⁻ g).coeFn_toLp 2] with x h₁ h₂ h₃
  rw [h₁, h₃]
  exact h₂

/-- The Fourier transform preserves even parity, so the same odd-observable
argument applies in momentum coordinates. -/
theorem waveParity_fourier_of_even {m : ℕ} {f : WaveSpace m}
    (hf : waveParity m f = f) : waveParity m (waveFourier m f) = waveFourier m f := by
  have hsq : waveFourier m (waveFourier m f) = waveParity m f := by
    have h := waveParity_fourier_eq_inverse m (waveFourier m f)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    have he := congrArg (waveParity m) h
    simpa only [waveParity_involution] using he
  rw [waveParity_fourier_eq_inverse]
  apply (waveFourier m).injective
  rw [LinearIsometryEquiv.apply_symm_apply, hsq, hf]

/-- Every existing odd momentum moment of an even wavefunction vanishes.
Physical momentum is `2π` times the Fourier variable with Mathlib's
normalization, which is covered by the arbitrary odd multiplier. -/
theorem integral_odd_fourier_of_waveParity_eq_self {m : ℕ} {f : WaveSpace m}
    (hf : waveParity m f = f) (a : WaveConfig m → ℝ)
    (ha : ∀ x, a (-x) = -a x)
    (hint : Integrable (fun x => a x * ‖waveFourier m f x‖ ^ 2) volume) :
    ∫ x, a x * ‖waveFourier m f x‖ ^ 2 = 0 :=
  integral_odd_of_waveParity_eq_self (waveParity_fourier_of_even hf) a ha hint

/-- Position and momentum first moments of the reduced difference output
vanish. The moments are the sums of the diagonal expectations in its
canonical Gram representation. Integrability expresses existence of each
term; in particular the conclusion applies whenever the first moments exist
absolutely. Momentum is `2π` times the Fourier variable. -/
theorem schrodingerReducedState_firstMoments {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (k : Fin m)
    (hx : ∀ i, Integrable (fun x : WaveConfig m => x k *
      ‖HilbertDensity.rightColumn b b
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i x‖ ^ 2) volume)
    (hp : ∀ i, Integrable (fun x : WaveConfig m => (2 * Real.pi * x k) *
      ‖waveFourier m (HilbertDensity.rightColumn b b
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i) x‖ ^ 2) volume) :
    (∑' i, ∫ x : WaveConfig m, x k *
      ‖HilbertDensity.rightColumn b b
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i x‖ ^ 2) = 0 ∧
    (∑' i, ∫ x : WaveConfig m, (2 * Real.pi * x k) *
      ‖waveFourier m (HilbertDensity.rightColumn b b
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i) x‖ ^ 2) = 0 := by
  constructor
  · have hzero : ∀ i, (∫ x : WaveConfig m, x k *
        ‖HilbertDensity.rightColumn b b
          ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i x‖ ^ 2) = 0 := by
      intro i
      exact integral_odd_of_waveParity_eq_self (schrodingerDifference_column_even b ψ i)
        (fun x => x k) (by intro x; rfl) (hx i)
    simp only [hzero, tsum_zero]
  · have hzero : ∀ i, (∫ x : WaveConfig m, (2 * Real.pi * x k) *
        ‖waveFourier m (HilbertDensity.rightColumn b b
          ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i) x‖ ^ 2) = 0 := by
      intro i
      exact integral_odd_fourier_of_waveParity_eq_self (schrodingerDifference_column_even b ψ i)
        (fun x => 2 * Real.pi * x k) (by intro x; simp) (hp i)
    simp only [hzero, tsum_zero]

/-- The position density of a countable Gram family of wavefunctions. The
nonnegative extended sum is finite almost everywhere for a summable family. -/
def waveGramDensity {m : ℕ} {ι : Type*} (g : ι → WaveSpace m) (x : WaveConfig m) : ℝ :=
  (∑' i, ENNReal.ofReal (‖g i x‖ ^ 2)).toReal

private theorem wave_integrable_norm_sq {m : ℕ} (f : WaveSpace m) :
    Integrable (fun x => ‖f x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

private theorem wave_integral_norm_sq {m : ℕ} (f : WaveSpace m) :
    (∫ x : WaveConfig m, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => norm_sq_eq_re_inner (𝕜 := ℂ) (f x)

private theorem waveGramDensity_aemeasurable_sum {m : ℕ} {ι : Type*} [Countable ι]
    (g : ι → WaveSpace m) :
    AEMeasurable (fun x => ∑' i, ENNReal.ofReal (‖g i x‖ ^ 2)) volume :=
  AEMeasurable.tsum (fun i => ((Lp.aestronglyMeasurable (g i)).norm.pow 2).aemeasurable.ennreal_ofReal)

private theorem waveGramDensity_lintegral {m : ℕ} {ι : Type*} [Countable ι]
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g) :
    (∫⁻ x, ∑' i, ENNReal.ofReal (‖g i x‖ ^ 2)) = ENNReal.ofReal (∑' i, ‖g i‖ ^ 2) := by
  rw [lintegral_tsum]
  · rw [ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg ‖g i‖) hg]
    apply tsum_congr
    intro i
    rw [← ofReal_integral_eq_lintegral_ofReal (wave_integrable_norm_sq (g i))
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖g i x‖), wave_integral_norm_sq]
  · intro i
    exact ((Lp.aestronglyMeasurable (g i)).norm.pow 2).aemeasurable.ennreal_ofReal

private theorem waveGramDensity_sum_ne_top {m : ℕ} {ι : Type*} [Countable ι]
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g) :
    ∀ᵐ x ∂volume, (∑' i, ENNReal.ofReal (‖g i x‖ ^ 2)) ≠ ⊤ := by
  have h := ae_lt_top' (waveGramDensity_aemeasurable_sum g)
    (by rw [waveGramDensity_lintegral hg]; exact ENNReal.ofReal_ne_top)
  exact h.mono (fun _ hx => hx.ne)

/-- The Gram position density is integrable. -/
theorem waveGramDensity_integrable {m : ℕ} {ι : Type*} [Countable ι]
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g) :
    Integrable (waveGramDensity g) volume :=
  integrable_toReal_of_lintegral_ne_top (waveGramDensity_aemeasurable_sum g)
    (by rw [waveGramDensity_lintegral hg]; exact ENNReal.ofReal_ne_top)

/-- The mass of the position density is the trace of its Gram operator. -/
theorem waveGramDensity_integral {m : ℕ} {ι : Type*} [Countable ι]
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g) :
    (∫ x, waveGramDensity g x) = ∑' i, ‖g i‖ ^ 2 := by
  unfold waveGramDensity
  rw [integral_toReal (waveGramDensity_aemeasurable_sum g)
    ((waveGramDensity_sum_ne_top hg).mono fun _ hx => lt_top_iff_ne_top.mpr hx),
    waveGramDensity_lintegral hg, ENNReal.toReal_ofReal]
  exact tsum_nonneg (fun i => sq_nonneg ‖g i‖)

/-- Each component density is bounded by the full Gram density almost everywhere. -/
theorem waveGramDensity_component_le {m : ℕ} {ι : Type*} [Countable ι]
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g) (i : ι) :
    ∀ᵐ x ∂volume, ‖g i x‖ ^ 2 ≤ waveGramDensity g x := by
  filter_upwards [waveGramDensity_sum_ne_top hg] with x hx
  have h := ENNReal.toReal_mono hx (ENNReal.le_tsum (f := fun j => ENNReal.ofReal (‖g j x‖ ^ 2)) i :
    ENNReal.ofReal (‖g i x‖ ^ 2) ≤ ∑' j, ENNReal.ofReal (‖g j x‖ ^ 2))
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), waveGramDensity] using h

/-- Existence of a global absolute moment implies existence of every Gram
component moment, so no column-integrability assumption is needed separately. -/
theorem waveGramDensity_integrable_component_moment {m : ℕ} {ι : Type*} [Countable ι]
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g)
    {a : WaveConfig m → ℝ} (ha : AEStronglyMeasurable a volume)
    (hint : Integrable (fun x => a x * waveGramDensity g x) volume) (i : ι) :
    Integrable (fun x => a x * ‖g i x‖ ^ 2) volume := by
  apply hint.mono (ha.mul ((Lp.aestronglyMeasurable (g i)).norm.pow 2))
  filter_upwards [waveGramDensity_component_le hg i] with x hx
  change ‖a x * ‖g i x‖ ^ 2‖ ≤ ‖a x * waveGramDensity g x‖
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖g i x‖)]
  exact mul_le_mul_of_nonneg_left (hx.trans (le_abs_self _)) (abs_nonneg _)

/-- Even Gram vectors have an even global position density. -/
theorem waveGramDensity_even {m : ℕ} {ι : Type*} [Countable ι]
    (g : ι → WaveSpace m) (heven : ∀ i, waveParity m (g i) = g i) :
    (fun x => waveGramDensity g (-x)) =ᵐ[volume] waveGramDensity g := by
  have he : ∀ i, (fun x => g i (-x)) =ᵐ[volume] g i := by
    intro i
    simpa only [heven i] using (waveParity_coeFn m (g i)).symm
  filter_upwards [eventually_countable_forall.mpr he] with x hx
  simp only [waveGramDensity, hx]

/-- Odd observables have zero global expectation in an even density whenever
the corresponding absolute first moment exists. -/
theorem integral_odd_mul_even_density {m : ℕ} {d a : WaveConfig m → ℝ}
    (hd : (fun x => d (-x)) =ᵐ[volume] d) (ha : ∀ x, a (-x) = -a x)
    (_hint : Integrable (fun x => a x * d x) volume) :
    (∫ x, a x * d x) = 0 := by
  have hneg : (∫ x, a (-x) * d (-x)) = ∫ x, a x * d x :=
    integral_neg_eq_self (fun x : WaveConfig m => a x * d x) volume
  have hodd : (∫ x, a (-x) * d (-x)) = -(∫ x, a x * d x) := by
    calc
      _ = ∫ x, -(a x * d x) := by
        apply integral_congr_ae
        filter_upwards [hd] with x hx
        rw [ha, hx, neg_mul]
      _ = _ := integral_neg _
  linarith

/-- Position density of the reduced difference state, in its canonical Gram representation. -/
def schrodingerDifferenceDensity {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) : WaveConfig m → ℝ :=
  waveGramDensity (HilbertDensity.rightColumn b b
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)))

/-- Fourier-coordinate density of the reduced difference state. Physical
momentum is `2π` times this Fourier coordinate. -/
def schrodingerDifferenceFourierDensity {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) : WaveConfig m → ℝ :=
  waveGramDensity (fun i => waveFourier m (HilbertDensity.rightColumn b b
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i))

/-- Both global densities have the reduced state's trace as their total mass. -/
theorem schrodingerDifferenceDensity_total {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) :
    (∫ x, schrodingerDifferenceDensity b ψ x) = HilbertDensity.positiveTrace b (schrodingerReducedState b ψ) ∧
    (∫ x, schrodingerDifferenceFourierDensity b ψ x) = HilbertDensity.positiveTrace b (schrodingerReducedState b ψ) := by
  have hg := HilbertDensity.rightColumn_gramFam b b
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ))
  have hgf : HilbertDensity.GramFam (fun i => waveFourier m (HilbertDensity.rightColumn b b
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i)) := by
    simpa only [HilbertDensity.GramFam, LinearIsometryEquiv.norm_map] using hg
  have ht : HilbertDensity.positiveTrace b (schrodingerReducedState b ψ) =
      ∑' i, ‖HilbertDensity.rightColumn b b
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i‖ ^ 2 :=
    HilbertDensity.positiveTrace_gramOp b hg
  constructor
  · exact (waveGramDensity_integral hg).trans ht.symm
  · simpa only [schrodingerDifferenceFourierDensity, LinearIsometryEquiv.norm_map] using (waveGramDensity_integral hgf).trans
      (by simpa only [LinearIsometryEquiv.norm_map] using ht.symm)

/-- The actual global position and momentum first moments of the difference
output vanish whenever their absolute moments exist. -/
theorem schrodingerReducedState_globalFirstMoments {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (k : Fin m)
    (hx : Integrable (fun x : WaveConfig m => x k * schrodingerDifferenceDensity b ψ x) volume)
    (hp : Integrable (fun x : WaveConfig m => (2 * Real.pi * x k) * schrodingerDifferenceFourierDensity b ψ x) volume) :
    (∫ x : WaveConfig m, x k * schrodingerDifferenceDensity b ψ x) = 0 ∧
    (∫ x : WaveConfig m, (2 * Real.pi * x k) * schrodingerDifferenceFourierDensity b ψ x) = 0 := by
  constructor
  · exact integral_odd_mul_even_density
      (waveGramDensity_even _ (schrodingerDifference_column_even b ψ)) (fun x => rfl) hx
  · exact integral_odd_mul_even_density
      (waveGramDensity_even _ (fun i => waveParity_fourier_of_even (schrodingerDifference_column_even b ψ i)))
      (by intro x; simp) hp

/-- The position event operator is multiplication by its measurable-set indicator. -/
def wavePositionEvent {m : ℕ} (s : Set (WaveConfig m)) (hs : MeasurableSet s) :
    WaveSpace m →L[ℂ] WaveSpace m := by
  let A : WaveSpace m →ₗ[ℂ] WaveSpace m :=
    { toFun := fun f => ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).indicator hs.nullMeasurableSet),
          Lp.coeFn_add (((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f))
            (((Lp.memLp g).indicator hs.nullMeasurableSet).toLp (s.indicator g)),
          MemLp.coeFn_toLp ((Lp.memLp f).indicator hs.nullMeasurableSet),
          MemLp.coeFn_toLp ((Lp.memLp g).indicator hs.nullMeasurableSet), Lp.coeFn_add f g] with x h₁ h₂ h₃ h₄ h₅
        rw [h₁, h₂]
        simp only [Pi.add_apply]
        rw [h₃, h₄]
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          exact h₅
        · simp [hx]
      map_smul' := by
        intro z f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (z • f)).indicator hs.nullMeasurableSet),
          Lp.coeFn_smul z (((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)),
          MemLp.coeFn_toLp ((Lp.memLp f).indicator hs.nullMeasurableSet), Lp.coeFn_smul z f] with x h₁ h₂ h₃ h₄
        simp only [RingHom.id_apply]
        rw [h₁, h₂]
        simp only [Pi.smul_apply]
        rw [h₃]
        by_cases hx : x ∈ s <;> simp [hx, h₄] }
  refine A.mkContinuous 1 ?_
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f).indicator hs.nullMeasurableSet)] with x hx
  change ‖(((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)) x‖ ≤ 1 * ‖f x‖
  rw [hx, one_mul]
  exact norm_indicator_le_norm_self _ _

theorem wavePositionEvent_coeFn {m : ℕ} (s : Set (WaveConfig m)) (hs : MeasurableSet s)
    (f : WaveSpace m) : (wavePositionEvent s hs f : WaveConfig m → ℂ) =ᵐ[volume] s.indicator f :=
  MemLp.coeFn_toLp ((Lp.memLp f).indicator hs.nullMeasurableSet)

/-- The Born probability of a position event is the integral of squared amplitude. -/
theorem wavePositionEvent_expectation {m : ℕ} (s : Set (WaveConfig m)) (hs : MeasurableSet s)
    (f : WaveSpace m) :
    (inner ℂ f (wavePositionEvent s hs f)).re = ∫ x in s, ‖f x‖ ^ 2 := by
  change RCLike.re (inner ℂ f (wavePositionEvent s hs f)) = _
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) f (wavePositionEvent s hs f)),
    ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [wavePositionEvent_coeFn s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs, norm_sq_eq_re_inner (𝕜 := ℂ)]
  · simp [Set.indicator_of_notMem hxs]

/-- The Gram density agrees with the real sum of the component densities. -/
theorem waveGramDensity_eq_tsum {m : ℕ} {ι : Type*} (g : ι → WaveSpace m) (x : WaveConfig m) :
    waveGramDensity g x = ∑' i, ‖g i x‖ ^ 2 := by
  rw [waveGramDensity, ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
  exact tsum_congr (fun i => ENNReal.toReal_ofReal (sq_nonneg _))

private theorem waveGramDensity_setIntegral {m : ℕ} {ι : Type*} [Countable ι]
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g) (s : Set (WaveConfig m)) :
    (∫ x in s, waveGramDensity g x) = ∑' i, ∫ x in s, ‖g i x‖ ^ 2 := by
  simp only [waveGramDensity_eq_tsum]
  apply (integral_tsum_of_summable_integral_norm
    (fun i => (wave_integrable_norm_sq (g i)).restrict) ?_).symm
  apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _)) _ hg
  intro i
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  rw [← wave_integral_norm_sq]
  exact setIntegral_le_integral (wave_integrable_norm_sq (g i))
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖g i x‖)

/-- Position probabilities computed from the reduced density operator are
exactly the integrals of its Gram density. This identifies the global density
with the actual position distribution, not merely the columnwise moments. -/
theorem operatorTrace_wavePositionEvent_gramOp {m : ℕ} {ι κ : Type*} [Countable ι]
    (b : HilbertBasis κ ℂ (WaveSpace m)) {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g)
    (s : Set (WaveConfig m)) (hs : MeasurableSet s) :
    (HilbertDensity.operatorTrace b (wavePositionEvent s hs * HilbertDensity.gramOp b g hg)).re =
      ∫ x in s, waveGramDensity g x := by
  rw [HilbertDensity.operatorTrace_mul_gramOp]
  have hsum : Summable (fun i => inner ℂ (g i) (wavePositionEvent s hs (g i))) := by
    apply Summable.of_norm_bounded (hg.mul_left ‖wavePositionEvent s hs‖)
    intro i
    calc
      ‖inner ℂ (g i) (wavePositionEvent s hs (g i))‖ ≤ ‖g i‖ * ‖wavePositionEvent s hs (g i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖g i‖ * (‖wavePositionEvent s hs‖ * ‖g i‖) :=
        mul_le_mul_of_nonneg_left ((wavePositionEvent s hs).le_opNorm _) (norm_nonneg _)
      _ = ‖wavePositionEvent s hs‖ * ‖g i‖ ^ 2 := by ring
  rw [Complex.re_tsum hsum, waveGramDensity_setIntegral hg]
  exact tsum_congr (fun i => wavePositionEvent_expectation s hs (g i))

/-- The position-event probability of the reduced difference state is its
explicit global density integrated over that event. -/
theorem schrodingerDifferenceDensity_positionEvent {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m)
    (s : Set (WaveConfig m)) (hs : MeasurableSet s) :
    (HilbertDensity.operatorTrace b (wavePositionEvent s hs * schrodingerReducedState b ψ)).re =
      ∫ x in s, schrodingerDifferenceDensity b ψ x :=
  operatorTrace_wavePositionEvent_gramOp b (HilbertDensity.rightColumn_gramFam b b _) s hs

/-- A Fourier-coordinate event, pulled back to the original wavefunction.
Physical momentum events use the corresponding set scaled by `2π`. -/
def waveFourierEvent {m : ℕ} (s : Set (WaveConfig m)) (hs : MeasurableSet s) :
    WaveSpace m →L[ℂ] WaveSpace m :=
  (waveFourier m).symm.toLinearIsometry.toContinuousLinearMap ∘L
    wavePositionEvent s hs ∘L (waveFourier m).toLinearIsometry.toContinuousLinearMap

/-- The Fourier-coordinate probability density is the density of the Fourier-transformed
Gram vectors; the conjugated bounded event acts on the original density operator. -/
theorem operatorTrace_waveFourierEvent_gramOp {m : ℕ} {ι κ : Type*} [Countable ι]
    (b : HilbertBasis κ ℂ (WaveSpace m)) {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g)
    (s : Set (WaveConfig m)) (hs : MeasurableSet s) :
    (HilbertDensity.operatorTrace b (waveFourierEvent s hs * HilbertDensity.gramOp b g hg)).re =
      ∫ x in s, waveGramDensity (fun i => waveFourier m (g i)) x := by
  have hgf : HilbertDensity.GramFam (fun i => waveFourier m (g i)) := by
    simpa only [HilbertDensity.GramFam, LinearIsometryEquiv.norm_map] using hg
  rw [← operatorTrace_wavePositionEvent_gramOp b hgf s hs]
  congr 1
  rw [HilbertDensity.operatorTrace_mul_gramOp, HilbertDensity.operatorTrace_mul_gramOp]
  apply tsum_congr
  intro i
  exact ((waveFourier m).inner_map_eq_flip (g i) (wavePositionEvent s hs (waveFourier m (g i)))).symm

/-- The bounded momentum-coordinate event probabilities of the reduced
state are the integrals of the stated Fourier-coordinate density. -/
theorem schrodingerDifferenceFourierDensity_positionEvent {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m)
    (s : Set (WaveConfig m)) (hs : MeasurableSet s) :
    (HilbertDensity.operatorTrace b (waveFourierEvent s hs * schrodingerReducedState b ψ)).re =
      ∫ x in s, schrodingerDifferenceFourierDensity b ψ x :=
  operatorTrace_waveFourierEvent_gramOp b (HilbertDensity.rightColumn_gramFam b b _) s hs

/-- For normalized input, both explicitly identified outcome densities have mass one. -/
theorem schrodingerDifferenceDensity_normalized {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    (∫ x, schrodingerDifferenceDensity b ψ x) = 1 ∧
    (∫ x, schrodingerDifferenceFourierDensity b ψ x) = 1 := by
  have h := schrodingerDifferenceDensity_total b ψ
  rw [(schrodingerReducedState_isDensityOperator b ψ hψ).trace_eq_one] at h
  exact h

/-- The global moment hypotheses imply the older columnwise hypotheses and
therefore also the two Gram-sum formulas for the mean. -/
theorem schrodingerReducedState_firstMoments_of_global {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (k : Fin m)
    (hx : Integrable (fun x : WaveConfig m => x k * schrodingerDifferenceDensity b ψ x) volume)
    (hp : Integrable (fun x : WaveConfig m => (2 * Real.pi * x k) * schrodingerDifferenceFourierDensity b ψ x) volume) :
    (∑' i, ∫ x : WaveConfig m, x k *
      ‖HilbertDensity.rightColumn b b
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i x‖ ^ 2) = 0 ∧
    (∑' i, ∫ x : WaveConfig m, (2 * Real.pi * x k) *
      ‖waveFourier m (HilbertDensity.rightColumn b b
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i) x‖ ^ 2) = 0 := by
  have hg := HilbertDensity.rightColumn_gramFam b b
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ))
  have hgf : HilbertDensity.GramFam (fun i => waveFourier m (HilbertDensity.rightColumn b b
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) i)) := by
    simpa only [HilbertDensity.GramFam, LinearIsometryEquiv.norm_map] using hg
  apply schrodingerReducedState_firstMoments b ψ k
  · exact waveGramDensity_integrable_component_moment hg (by fun_prop) hx
  · exact waveGramDensity_integrable_component_moment hgf (by fun_prop) hp

end
end GaussianTesting
