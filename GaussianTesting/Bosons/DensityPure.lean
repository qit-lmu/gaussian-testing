module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.HilbertDensity

@[expose] public section

/-!
# Pure density operators at operator norm one

The exact purity reduction in Proposition 6.3 uses this elementary consequence
of trace one and positivity. Compactness supplies a top eigenvector; trace one
forces its orthogonal residual to vanish.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable {ι κ : Type*}

private theorem norm_residualFam_sq {g : ι → L2 κ} {ξ : L2 κ} (hξ : ‖ξ‖ = 1) (i : ι) :
    ‖residualFam g ξ i‖ ^ 2 = ‖g i‖ ^ 2 - ‖inner ℂ (g i) ξ‖ ^ 2 := by
  rw [residualFam, @norm_sub_sq ℂ, norm_smul, hξ, mul_one, inner_smul_right,
    ← inner_conj_symm (g i) ξ, Complex.mul_conj]
  simp only [Complex.normSq_eq_norm_sq, Complex.norm_conj]
  change ‖g i‖ ^ 2 - 2 * ‖inner ℂ ξ (g i)‖ ^ 2 + ‖inner ℂ ξ (g i)‖ ^ 2 =
    ‖g i‖ ^ 2 - ‖inner ℂ ξ (g i)‖ ^ 2
  ring

/-- A normalized Gram operator with norm one is a rank-one projection. -/
theorem gramOp_eq_rankOne_of_norm_eq_one {g : ι → L2 κ} (hg : GramFam g)
    (hmass : ∑' i, ‖g i‖^2 = 1) (hnorm : ‖gramOp g hg‖ = 1) :
    ∃ ξ : L2 κ, ‖ξ‖ = 1 ∧ gramOp g hg = InnerProductSpace.rankOne ℂ ξ ξ := by
  have hne : gramOp g hg ≠ 0 := by
    intro h
    simp only [h, norm_zero, zero_ne_one] at hnorm
  obtain ⟨ξ,hξ,heig⟩ := exists_top_eigenvector hg hne
  have hs : Summable (fun i => ‖inner ℂ (g i) ξ‖^2) := by
    apply hg.of_nonneg_of_le (fun i => sq_nonneg _)
    intro i
    have h := norm_inner_le_norm (𝕜 := ℂ) (g i) ξ
    rw [hξ, mul_one] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hmassξ : ∑' i, ‖inner ℂ (g i) ξ‖^2 = 1 := by
    have h := congrArg Complex.re (inner_gramOp_self hg ξ)
    simpa [heig, hnorm, inner_self_eq_norm_sq_to_K, hξ] using h.symm
  have hr : ∑' i, ‖residualFam g ξ i‖^2 = 0 := by
    simp_rw [norm_residualFam_sq hξ]
    rw [hg.tsum_sub hs, hmass, hmassξ, sub_self]
  have hz : gramOp (residualFam g ξ) (residualFam_gramFam hg ξ) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm ((gramOp_norm_le (residualFam_gramFam hg ξ)).trans_eq hr)
      (norm_nonneg _)
  refine ⟨ξ,hξ,?_⟩
  ext x : 1
  rw [gramOp_eq_top_add_residual hg hξ heig x, hnorm, Complex.ofReal_one,
    one_smul, hz, zero_apply, add_zero]
  rfl

namespace HilbertDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A density operator of norm one is pure, on any complete complex Hilbert
space; the supplied Hilbert basis only defines its trace. -/
theorem IsDensityOperator.exists_rankOne_of_norm_eq_one
    {b : HilbertBasis κ ℂ E} {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ)
    (hnorm : ‖ρ‖ = 1) :
    ∃ ξ : E, ‖ξ‖ = 1 ∧ ρ = InnerProductSpace.rankOne ℂ ξ ξ := by
  obtain ⟨g,hg,hrep,hmass⟩ := hρ.toIsPositiveTraceClass.exists_gram_representation
  have hmass' : ∑' i, ‖g i‖^2 = 1 := hmass.trans hρ.trace_eq_one
  have hn : ‖GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b)‖ = 1 := by
    rw [← inBasis_gramOp b g hg, inBasis_norm, hrep, hnorm]
  obtain ⟨v,hv,he⟩ := gramOp_eq_rankOne_of_norm_eq_one (hg.inBasis b)
    (by simpa only [b.repr.norm_map] using hmass') hn
  refine ⟨b.repr.symm v, by simpa only [b.repr.symm.norm_map] using hv, ?_⟩
  have hop : inBasis b ρ = InnerProductSpace.rankOne ℂ v v := by
    rw [← hrep, inBasis_gramOp, he]
  ext x : 1
  apply b.repr.injective
  have h := congrArg (fun A : L2 κ →L[ℂ] L2 κ => A (b.repr x)) hop
  have hi : inner ℂ v (b.repr x) = inner ℂ (b.repr.symm v) x := by
    rw [← b.repr.symm.inner_map_map v (b.repr x), b.repr.symm_apply_apply]
  simpa only [inBasis_apply, b.repr.symm_apply_apply, InnerProductSpace.rankOne_apply,
    map_smul, b.repr.apply_symm_apply, hi] using h

end HilbertDensity
end
end GaussianTesting
