module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Density

@[expose] public section

/-!
# Tensor products of positive trace-class operators

The product of the canonical square-root Gram families constructs the tensor
product operator. Its action on elementary tensors is `ρ x ⊗ σ y`, which
uniquely characterizes a bounded operator on the completed tensor product.
Consequently every choice of Gram representations yields this same operator.
Its positive trace is the product of the two traces, so density operators
give a density operator on two copies, as required for Lemma 6.2.
-/

namespace GaussianTesting

open scoped InnerProductSpace

variable {ι ι' κ κ' : Type*}

private theorem gram_coeff_coordinate {g : ι → L2 κ} (hg : GramFam g)
    (x : L2 κ) (j : κ) :
    ∑' k, inner ℂ (g k) x * g k j = gramOp g hg x j := by
  exact ((hg.summable_coeff x).hasSum.mapL
    (lp.evalCLM ℂ (fun _ : κ => ℂ) 2 j)).tsum_eq

private theorem gram_coeff_coordinate_summable {g : ι → L2 κ} (hg : GramFam g)
    (x : L2 κ) (j : κ) : Summable (fun k => inner ℂ (g k) x * g k j) := by
  exact ((hg.summable_coeff x).hasSum.mapL
    (lp.evalCLM ℂ (fun _ : κ => ℂ) 2 j)).summable

/-- The product Gram family acts as the tensor product on elementary tensors. -/
theorem gramOp_tensorFam_tp {g : ι → L2 κ} {f : ι' → L2 κ'}
    (hg : GramFam g) (hf : GramFam f) (x : L2 κ) (y : L2 κ') :
    gramOp (tensorFam g f) (tensorFam_gramFam hg hf) (tpPair x y) =
      tpPair (gramOp g hg x) (gramOp f hf y) := by
  apply lp.ext
  funext p
  rw [← gram_coeff_coordinate (tensorFam_gramFam hg hf) (tpPair x y) p]
  simp only [tensorFam, inner_tpPair, tpPair_apply]
  rw [← gram_coeff_coordinate hg x p.1, ← gram_coeff_coordinate hf y p.2]
  simpa only [mul_mul_mul_comm] using
    (tsum_mul_tsum_of_summable_norm (gram_coeff_coordinate_summable hg x p.1).norm
      (gram_coeff_coordinate_summable hf y p.2).norm).symm

/-- Bounded operators on the product space are determined by elementary tensors. -/
theorem tensorOperator_ext {A B : L2 (κ × κ') →L[ℂ] L2 (κ × κ')}
    (h : ∀ (x : L2 κ) (y : L2 κ'), A (tpPair x y) = B (tpPair x y)) : A = B := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num)
  intro p
  apply ContinuousLinearMap.ext
  intro z
  change A (lp.single 2 p z) = B (lp.single 2 p z)
  have hs : (lp.single 2 p z : L2 (κ × κ')) =
      tpPair (lp.single 2 p.1 z) (lp.single 2 p.2 1) := by
    apply lp.ext
    funext q
    simp only [tpPair_apply, lp.single_apply]
    by_cases h1 : q.1 = p.1 <;> by_cases h2 : q.2 = p.2 <;>
      simp_all [Prod.ext_iff, Pi.single_apply]
  rw [hs]
  exact h _ _

/-- Tensor product of positive trace-class operators, constructed from the
columns of their positive square roots. `densityTensor_tp` characterizes it
without referring to these Gram families. -/
noncomputable def densityTensor (ρ : L2 κ →L[ℂ] L2 κ) (σ : L2 κ' →L[ℂ] L2 κ')
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ) :
    L2 (κ × κ') →L[ℂ] L2 (κ × κ') :=
  gramOp (tensorFam (sqrtGramFamily ρ (l2HilbertBasis κ))
    (sqrtGramFamily σ (l2HilbertBasis κ')))
    (tensorFam_gramFam
      (sqrtGramFamily_gramFam hρ.nonneg (l2HilbertBasis κ) hρ.summable_diagonal)
      (sqrtGramFamily_gramFam hσ.nonneg (l2HilbertBasis κ') hσ.summable_diagonal))

/-- The constructed operator has the defining tensor-product action. -/
theorem densityTensor_tp (ρ : L2 κ →L[ℂ] L2 κ) (σ : L2 κ' →L[ℂ] L2 κ')
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    (x : L2 κ) (y : L2 κ') :
    densityTensor ρ σ hρ hσ (tpPair x y) = tpPair (ρ x) (σ y) := by
  rw [densityTensor, gramOp_tensorFam_tp
    (sqrtGramFamily_gramFam hρ.nonneg (l2HilbertBasis κ) hρ.summable_diagonal)
    (sqrtGramFamily_gramFam hσ.nonneg (l2HilbertBasis κ') hσ.summable_diagonal),
    gramOp_sqrtGramFamily hρ.nonneg (l2HilbertBasis κ) hρ.summable_diagonal,
    gramOp_sqrtGramFamily hσ.nonneg (l2HilbertBasis κ') hσ.summable_diagonal]

/-- The tensor operator is independent of both Gram representations. -/
theorem densityTensor_eq_gramOp_tensorFam
    {ρ : L2 κ →L[ℂ] L2 κ} {σ : L2 κ' →L[ℂ] L2 κ'}
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    {g : ι → L2 κ} {f : ι' → L2 κ'} (hg : GramFam g) (hf : GramFam f)
    (hgrepr : gramOp g hg = ρ) (hfrepr : gramOp f hf = σ) :
    densityTensor ρ σ hρ hσ = gramOp (tensorFam g f) (tensorFam_gramFam hg hf) := by
  apply tensorOperator_ext
  intro x y
  rw [densityTensor_tp, gramOp_tensorFam_tp hg hf, hgrepr, hfrepr]

/-- The elementary-tensor action uniquely specifies the constructed operator. -/
theorem densityTensor_unique
    (ρ : L2 κ →L[ℂ] L2 κ) (σ : L2 κ' →L[ℂ] L2 κ')
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ)
    {A : L2 (κ × κ') →L[ℂ] L2 (κ × κ')}
    (hA : ∀ x y, A (tpPair x y) = tpPair (ρ x) (σ y)) :
    A = densityTensor ρ σ hρ hσ := by
  apply tensorOperator_ext
  intro x y
  rw [hA, densityTensor_tp]

/-- The tensor product of two positive trace-class operators is positive trace class. -/
theorem isPositiveTraceClass_densityTensor
    (ρ : L2 κ →L[ℂ] L2 κ) (σ : L2 κ' →L[ℂ] L2 κ')
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ) :
    IsPositiveTraceClass (densityTensor ρ σ hρ hσ) :=
  isPositiveTraceClass_gramOp _

private theorem tensorFam_mass {g : ι → L2 κ} {f : ι' → L2 κ'}
    (hg : GramFam g) (hf : GramFam f) :
    ∑' p, ‖tensorFam g f p‖ ^ 2 = (∑' i, ‖g i‖ ^ 2) * ∑' j, ‖f j‖ ^ 2 := by
  simp only [tensorFam, norm_tpPair, mul_pow]
  have h := hg.mul_of_nonneg hf (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  rw [h.tsum_prod]
  simp_rw [tsum_mul_left, tsum_mul_right]

/-- The trace of a tensor product is the product of the positive traces. -/
theorem positiveTrace_densityTensor
    (ρ : L2 κ →L[ℂ] L2 κ) (σ : L2 κ' →L[ℂ] L2 κ')
    (hρ : IsPositiveTraceClass ρ) (hσ : IsPositiveTraceClass σ) :
    positiveTrace (densityTensor ρ σ hρ hσ) = positiveTrace ρ * positiveTrace σ := by
  obtain ⟨g, hg, hgrepr, hgmass⟩ := hρ.exists_gram_representation
  obtain ⟨f, hf, hfrepr, hfmass⟩ := hσ.exists_gram_representation
  rw [densityTensor_eq_gramOp_tensorFam hρ hσ hg hf hgrepr hfrepr,
    positiveTrace_gramOp, tensorFam_mass hg hf, hgmass, hfmass]

/-- Independent density operators give a normalized density operator on the product space. -/
theorem IsDensityOperator.densityTensor
    {ρ : L2 κ →L[ℂ] L2 κ} {σ : L2 κ' →L[ℂ] L2 κ'}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    IsDensityOperator (densityTensor ρ σ hρ.toIsPositiveTraceClass hσ.toIsPositiveTraceClass) := by
  refine ⟨isPositiveTraceClass_densityTensor _ _ _ _, ?_⟩
  rw [positiveTrace_densityTensor, hρ.trace_eq_one, hσ.trace_eq_one, mul_one]

end GaussianTesting
