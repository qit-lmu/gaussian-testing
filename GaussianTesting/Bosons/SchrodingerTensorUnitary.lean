module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerTensor
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-!
# Completeness of the wavefunction tensor representation

Finite-measure rectangle indicators determine an `L²` function on a product
measure space. Consequently the tensor-product realization of the two-copy
Schrödinger space is a unitary equivalence, as used when defining the physical
four-copy bosonic measurement in Section 6 of the manuscript.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace TensorProduct

noncomputable section

/-- Finite-measure rectangles determine an `L²` function on a product space. -/
private theorem l2_ae_zero_of_rectangle_integrals
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (f : Lp ℂ 2 (μ.prod ν))
    (h : ∀ (s : Set α) (t : Set β), MeasurableSet s → MeasurableSet t →
      μ s < ∞ → ν t < ∞ → ∫ z in s ×ˢ t, f z ∂(μ.prod ν) = 0) :
    (f : α × β → ℂ) =ᵐ[μ.prod ν] 0 := by
  have hlocal (s : Set α) (t : Set β) (hs : MeasurableSet s)
      (ht : MeasurableSet t) (hμs : μ s < ∞) (hνt : ν t < ∞) :
      (f : α × β → ℂ) =ᵐ[(μ.prod ν).restrict (s ×ˢ t)] 0 := by
    have hfinite : (μ.prod ν) (s ×ˢ t) < ∞ := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top hμs hνt
    let : IsFiniteMeasure ((μ.prod ν).restrict (s ×ˢ t)) :=
      ⟨by simpa using hfinite⟩
    have hf : Integrable (f : α × β → ℂ) ((μ.prod ν).restrict (s ×ˢ t)) :=
      ((Lp.memLp f).restrict _).integrable (by norm_num)
    have huniv : ∫ z, f z ∂((μ.prod ν).restrict (s ×ˢ t)) = 0 := h s t hs ht hμs hνt
    have hall (u : Set (α × β)) (hu : MeasurableSet u) :
        ∫ z in u, f z ∂((μ.prod ν).restrict (s ×ˢ t)) = 0 := by
      induction u, hu using MeasurableSpace.induction_on_inter
          generateFrom_prod.symm isPiSystem_prod with
      | empty => simp
      | basic u hu =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hu
        rw [Measure.restrict_restrict (ha.prod hb), Set.prod_inter_prod]
        exact h (a ∩ s) (b ∩ t) (ha.inter hs) (hb.inter ht)
          ((measure_mono Set.inter_subset_right).trans_lt hμs)
          ((measure_mono Set.inter_subset_right).trans_lt hνt)
      | compl u hu ihu => rw [setIntegral_compl hu hf, huniv, ihu, sub_self]
      | iUnion u hd hu ihu => rw [integral_iUnion hu hd hf.integrableOn]; simp [ihu]
    exact hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun u hu _ => hall u hu)
  have hexhaust (n k : ℕ) : ∀ᵐ z ∂(μ.prod ν),
      z ∈ spanningSets μ n ×ˢ spanningSets ν k → f z = 0 := by
    exact (ae_restrict_iff' ((measurableSet_spanningSets μ n).prod
      (measurableSet_spanningSets ν k))).1
        (hlocal _ _ (measurableSet_spanningSets μ n) (measurableSet_spanningSets ν k)
          (measure_spanningSets_lt_top μ n) (measure_spanningSets_lt_top ν k))
  filter_upwards [ae_all_iff.2 (fun n => ae_all_iff.2 (hexhaust n))] with z hz
  exact hz (spanningSetsIndex μ z.1) (spanningSetsIndex ν z.2)
    ⟨mem_spanningSetsIndex μ z.1, mem_spanningSetsIndex ν z.2⟩

/-- The product of two indicator functions represents the rectangle indicator. -/
private theorem productWave_indicator (m : ℕ) (s t : Set (WaveConfig m))
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : volume s < ∞) (hμt : volume t < ∞) :
    productWave (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
      (indicatorConstLp 2 ht hμt.ne (1 : ℂ)) =
    indicatorConstLp 2 (hs.prod ht)
      (by rw [Measure.prod_prod]; exact (ENNReal.mul_lt_top hμs hμt).ne) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [productWave_coeFn
      (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
      (indicatorConstLp 2 ht hμt.ne (1 : ℂ)),
    quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℂ))),
    quasiMeasurePreserving_snd.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hμt.ne) (c := (1 : ℂ))),
    (indicatorConstLp_coeFn (p := 2) (hs := hs.prod ht)
      (hμs := by rw [Measure.prod_prod]; exact (ENNReal.mul_lt_top hμs hμt).ne)
      (c := (1 : ℂ)))] with z hz hz₁ hz₂ hz₃
  simp only [Function.comp_apply] at hz₁ hz₂
  rw [hz, hz₁, hz₂, hz₃]
  by_cases hzs : z.1 ∈ s <;> by_cases hzt : z.2 ∈ t <;>
    simp [Set.indicator, hzs, hzt]

/-- Products span a dense subspace, and the completed tensor realization is onto. -/
theorem productWaveTensor_surjective (m : ℕ) :
    Function.Surjective (productWaveTensorIsometry m).fromCompletion := by
  let T := (productWaveTensorIsometry m).fromCompletion
  let R := T.toLinearMap.range
  have hclosed : IsClosed (R : Set (ProductWaveSpace m)) :=
    T.isometry.isUniformInducing.isComplete_range.isClosed
  let : CompleteSpace R := hclosed.completeSpace_coe
  have htop : R = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.1
    apply (Submodule.eq_bot_iff _).2
    intro f hf
    apply Lp.ext
    refine (l2_ae_zero_of_rectangle_integrals f ?_).trans (Lp.coeFn_zero _ _ _).symm
    intro s t hs ht hμs hμt
    have hrect : indicatorConstLp 2 (hs.prod ht)
        (by rw [Measure.prod_prod]; exact (ENNReal.mul_lt_top hμs hμt).ne)
        (1 : ℂ) ∈ R := by
      refine ⟨hilbertTmul (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
        (indicatorConstLp 2 ht hμt.ne (1 : ℂ)), ?_⟩
      exact ((productWaveTensorIsometry m).fromCompletion_apply_coe _).trans
        (productWave_indicator m s t hs ht hμs hμt)
    have hz := R.inner_right_of_mem_orthogonal hrect hf
    rwa [L2.inner_indicatorConstLp_one] at hz
  intro f
  have : f ∈ R := by rw [htop]; trivial
  exact this

/-- Every two-copy Schrödinger wavefunction is a completed Hilbert tensor. -/
theorem waveTensor_surjective (m : ℕ) : Function.Surjective (waveTensor m) := by
  let join : WaveConfig m × WaveConfig m → BosonConfig m :=
    fun xy => (splitConfigIsometry m).symm (WithLp.toLp 2 xy)
  have hjoin : MeasurePreserving join (volume.prod volume) volume :=
    (splitConfigIsometry m).symm.measurePreserving.comp
      (WithLp.volume_preserving_toLp (WaveConfig m) (WaveConfig m))
  intro f
  obtain ⟨v, hv⟩ := productWaveTensor_surjective m (Lp.compMeasurePreserving join hjoin f)
  refine ⟨v, ?_⟩
  change Lp.compMeasurePreserving _ (bosonPositions_measurePreserving m)
    ((productWaveTensorIsometry m).fromCompletion v) = f
  rw [hv, ← Lp.compMeasurePreserving_comp_apply]
  have hid : join ∘ (fun z : BosonConfig m =>
      (bosonPosition 0 z, bosonPosition 1 z)) = id := by
    funext z
    exact (splitConfigIsometry m).symm_apply_apply z
  simpa only [hid] using Lp.compMeasurePreserving_id_apply f

/-- The canonical unitary identification of the completed tensor square with
the actual two-copy Schrödinger wavefunctions. -/
def waveTensorEquiv (m : ℕ) :
    HilbertSquare (WaveSpace m) ≃ₗᵢ[ℂ] SchrodingerSpace m :=
  LinearIsometryEquiv.ofSurjective (waveTensor m) (waveTensor_surjective m)

@[simp] theorem waveTensorEquiv_apply (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    waveTensorEquiv m v = waveTensor m v := rfl

@[simp] theorem waveTensorEquiv_toLinearIsometry (m : ℕ) :
    (waveTensorEquiv m).toLinearIsometry = waveTensor m := rfl

end

end GaussianTesting
