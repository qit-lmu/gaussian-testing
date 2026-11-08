module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.GradientFlow.HilbertTensor
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

/-!
# Hilbert tensors of two L² spaces

The product of wavefunctions realizes the completed Hilbert tensor product
as L² of the product measure. The distinct factor spaces are needed when
regrouping one copy and two copies in the physical bosonic tensor cube.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace TensorProduct

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [sigmaFiniteμ : SigmaFinite μ] [sigmaFiniteν : SigmaFinite ν]

omit sigmaFiniteμ sigmaFiniteν in
private theorem productLp_memLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2
      (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : α × β => f z.1 * g z.2)
      (μ.prod ν) :=
    ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      quasiMeasurePreserving_fst).mul
        ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving quasiMeasurePreserving_snd)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_mul, mul_pow] using
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)).mul_prod
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g))

def productLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (show MemLp (fun z : α × β => f z.1 * g z.2) 2 (μ.prod ν) from by
    exact productLp_memLp f g).toLp _

omit sigmaFiniteμ sigmaFiniteν in
theorem productLp_coeFn (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    (productLp f g : α × β → ℂ) =ᵐ[μ.prod ν]
      fun z => f z.1 * g z.2 := (productLp_memLp f g).coeFn_toLp

private theorem inner_productLp (f f' : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    inner ℂ (productLp f g) (productLp f' g') = inner ℂ f f' * inner ℂ g g' := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def,
    MeasureTheory.L2.inner_def, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [productLp_coeFn f g, productLp_coeFn f' g'] with z h h'
  rw [h, h']
  simp only [RCLike.inner_apply, map_mul]
  ring

omit sigmaFiniteμ sigmaFiniteν in
private theorem productLp_add_left [SigmaFinite μ] [SigmaFinite ν] (f f' : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productLp (f + f') g = productLp f g + productLp f' g := by
  apply Lp.ext
  filter_upwards [productLp_coeFn (f + f') g, productLp_coeFn f g,
    productLp_coeFn f' g, Lp.coeFn_add (productLp f g) (productLp f' g),
    quasiMeasurePreserving_fst.ae (Lp.coeFn_add f f')] with z h h' h'' ha hf
  simp only [h, ha, h', h'', hf, Pi.add_apply, add_mul]

omit sigmaFiniteμ sigmaFiniteν in
private theorem productLp_smul_left [SigmaFinite μ] [SigmaFinite ν] (a : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productLp (a • f) g = a • productLp f g := by
  apply Lp.ext
  filter_upwards [productLp_coeFn (a • f) g, productLp_coeFn f g,
    Lp.coeFn_smul a (productLp f g),
    quasiMeasurePreserving_fst.ae (Lp.coeFn_smul a f)] with z h h' ha hf
  simp only [h, ha, h', hf, Pi.smul_apply, smul_eq_mul, mul_assoc]

omit sigmaFiniteμ sigmaFiniteν in
private theorem productLp_add_right [SigmaFinite μ] [SigmaFinite ν] (f : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    productLp f (g + g') = productLp f g + productLp f g' := by
  apply Lp.ext
  filter_upwards [productLp_coeFn f (g + g'), productLp_coeFn f g,
    productLp_coeFn f g', Lp.coeFn_add (productLp f g) (productLp f g'),
    quasiMeasurePreserving_snd.ae (Lp.coeFn_add g g')] with z h h' h'' ha hg
  simp only [h, ha, h', h'', hg, Pi.add_apply, mul_add]

omit sigmaFiniteμ sigmaFiniteν in
private theorem productLp_smul_right [SigmaFinite μ] [SigmaFinite ν] (a : ℂ) (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productLp f (a • g) = a • productLp f g := by
  apply Lp.ext
  filter_upwards [productLp_coeFn f (a • g), productLp_coeFn f g,
    Lp.coeFn_smul a (productLp f g),
    quasiMeasurePreserving_snd.ae (Lp.coeFn_smul a g)] with z h h' ha hg
  simp only [h, ha, h', hg, Pi.smul_apply, smul_eq_mul, mul_left_comm]

def productLpLinear (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mk₂ ℂ productLp (by exact productLp_add_left) (by exact productLp_smul_left)
    (by exact productLp_add_right) (by exact fun a f g => productLp_smul_right a f g)

def productLpTensorLinear (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] :
    (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν) →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  TensorProduct.lift (productLpLinear μ ν)

def productLpTensorIsometry (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] :
    (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  (productLpTensorLinear μ ν).isometryOfInner fun u v => by
    induction u using TensorProduct.inductionOn with
    | tmul f g =>
      induction v using TensorProduct.inductionOn with
      | tmul f' g' =>
        exact (inner_productLp f f' g g').trans (TensorProduct.inner_tmul ℂ f f' g g').symm
      | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]

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
private theorem productLp_indicator (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] (s : Set α) (t : Set β)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s < ∞) (hνt : ν t < ∞) :
    productLp (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
      (indicatorConstLp 2 ht hνt.ne (1 : ℂ)) =
    indicatorConstLp 2 (hs.prod ht)
      (by rw [Measure.prod_prod]; exact (ENNReal.mul_lt_top hμs hνt).ne) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [productLp_coeFn
      (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
      (indicatorConstLp 2 ht hνt.ne (1 : ℂ)),
    quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℂ))),
    quasiMeasurePreserving_snd.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := ht) (hμs := hνt.ne) (c := (1 : ℂ))),
    (indicatorConstLp_coeFn (p := 2) (hs := hs.prod ht)
      (hμs := by rw [Measure.prod_prod]; exact (ENNReal.mul_lt_top hμs hνt).ne)
      (c := (1 : ℂ)))] with z hz hz₁ hz₂ hz₃
  simp only [Function.comp_apply] at hz₁ hz₂
  rw [hz, hz₁, hz₂, hz₃]
  by_cases hzs : z.1 ∈ s <;> by_cases hzt : z.2 ∈ t <;>
    simp [Set.indicator, hzs, hzt]

/-- Products span a dense subspace, and the completed tensor realization is onto. -/
theorem productLpTensor_surjective (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] :
    Function.Surjective (productLpTensorIsometry μ ν).fromCompletion := by
  let T := (productLpTensorIsometry μ ν).fromCompletion
  let R := T.toLinearMap.range
  have hclosed : IsClosed (R : Set (Lp ℂ 2 (μ.prod ν))) :=
    T.isometry.isUniformInducing.isComplete_range.isClosed
  let : CompleteSpace R := hclosed.completeSpace_coe
  have htop : R = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.1
    apply (Submodule.eq_bot_iff _).2
    intro f hf
    apply Lp.ext
    refine (l2_ae_zero_of_rectangle_integrals f ?_).trans (Lp.coeFn_zero _ _ _).symm
    intro s t hs ht hμs hνt
    have hrect : indicatorConstLp 2 (hs.prod ht)
        (by rw [Measure.prod_prod]; exact (ENNReal.mul_lt_top hμs hνt).ne)
        (1 : ℂ) ∈ R := by
      refine ⟨hilbertTmul (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
        (indicatorConstLp 2 ht hνt.ne (1 : ℂ)), ?_⟩
      exact ((productLpTensorIsometry μ ν).fromCompletion_apply_coe _).trans
        (productLp_indicator μ ν s t hs ht hμs hνt)
    have hz := R.inner_right_of_mem_orthogonal hrect hf
    rwa [L2.inner_indicatorConstLp_one] at hz
  intro f
  have : f ∈ R := by rw [htop]; trivial
  exact this

/-- Products of L² functions give the canonical unitary onto the product space. -/
def productLpTensorEquiv (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] :
    HilbertTensor (Lp ℂ 2 μ) (Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective (productLpTensorIsometry μ ν).fromCompletion
    (productLpTensor_surjective μ ν)

@[simp] theorem productLpTensorEquiv_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    productLpTensorEquiv μ ν (hilbertTmul f g) = productLp f g :=
  (productLpTensorIsometry μ ν).fromCompletion_apply_coe (f ⊗ₜ[ℂ] g)

end
end GaussianTesting
