module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SignedSwapPurity
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

/-!
# Orthogonal-projection acceptance probabilities

For a positive trace-class operator, the trace against an orthogonal projection
is real and lies between zero and the positive trace. Thus the real-part notation
in the Lean statement of Lemma 6.2 is precisely the manuscript's real acceptance
probability, including when the density operator is written before the projection.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {κ ι : Type*} (K : Submodule ℂ E) [CompleteSpace K]

omit [CompleteSpace E] in
private lemma inner_starProjection_eq_norm_sq (x : E) :
    inner ℂ x (K.starProjection x) = (‖K.starProjection x‖ ^ 2 : ℝ) := by
  have h : inner ℂ x (K.starProjection x) =
      inner ℂ (K.starProjection x) (K.starProjection x) := by
    rw [Submodule.inner_starProjection_left_eq_right]
    rw [K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)]
  rw [h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The projection trace is the sum of the squared norms of the projected Gram
vectors. This also displays its reality and positivity. -/
theorem operatorTrace_starProjection_gramOp (b : HilbertBasis κ ℂ E)
    {g : ι → E} (hg : GramFam g) :
    operatorTrace b (K.starProjection * gramOp b g hg) =
      ((∑' i, ‖K.starProjection (g i)‖ ^ 2 : ℝ) : ℂ) := by
  rw [operatorTrace_mul_gramOp, Complex.ofReal_tsum]
  exact tsum_congr (fun i => inner_starProjection_eq_norm_sq K (g i))

/-- The trace of a positive trace-class operator against a projection is real. -/
theorem IsPositiveTraceClass.starProjection_trace_real
    {b : HilbertBasis κ ℂ E} {σ : E →L[ℂ] E} (hσ : IsPositiveTraceClass b σ) :
    operatorTrace b (K.starProjection * σ) =
      ((operatorTrace b (K.starProjection * σ)).re : ℂ) := by
  obtain ⟨g, hg, rfl, _⟩ := hσ.exists_gram_representation
  rw [operatorTrace_starProjection_gramOp]
  rfl

/-- The imaginary part of a projection expectation vanishes. -/
theorem IsPositiveTraceClass.starProjection_trace_im
    {b : HilbertBasis κ ℂ E} {σ : E →L[ℂ] E} (hσ : IsPositiveTraceClass b σ) :
    (operatorTrace b (K.starProjection * σ)).im = 0 := by
  rw [hσ.starProjection_trace_real K]
  rfl

/-- A projection expectation is nonnegative and at most the total positive trace. -/
theorem IsPositiveTraceClass.starProjection_trace_bounds
    {b : HilbertBasis κ ℂ E} {σ : E →L[ℂ] E} (hσ : IsPositiveTraceClass b σ) :
    0 ≤ (operatorTrace b (K.starProjection * σ)).re ∧
      (operatorTrace b (K.starProjection * σ)).re ≤ positiveTrace b σ := by
  obtain ⟨g, hg, rfl, _⟩ := hσ.exists_gram_representation
  rw [operatorTrace_starProjection_gramOp, Complex.ofReal_re, positiveTrace_gramOp]
  refine ⟨tsum_nonneg (fun _ => sq_nonneg _), ?_⟩
  exact (hg.map K.starProjection).tsum_le_tsum
    (fun i => pow_le_pow_left₀ (norm_nonneg _) (K.norm_starProjection_apply_le (g i)) 2) hg

/-- For a density operator, projection acceptance is a probability in `[0,1]`. -/
theorem IsDensityOperator.starProjection_probability
    {b : HilbertBasis κ ℂ E} {σ : E →L[ℂ] E} (hσ : IsDensityOperator b σ) :
    0 ≤ (operatorTrace b (K.starProjection * σ)).re ∧
      (operatorTrace b (K.starProjection * σ)).re ≤ 1 := by
  simpa only [hσ.trace_eq_one] using hσ.toIsPositiveTraceClass.starProjection_trace_bounds K

/-- Reality also holds with the manuscript's density-before-projection ordering. -/
theorem IsPositiveTraceClass.trace_starProjection_real
    {b : HilbertBasis κ ℂ E} {σ : E →L[ℂ] E} (hσ : IsPositiveTraceClass b σ) :
    operatorTrace b (σ * K.starProjection) =
      ((operatorTrace b (σ * K.starProjection)).re : ℂ) := by
  rw [← hσ.operatorTrace_mul_comm K.starProjection]
  exact hσ.starProjection_trace_real K

/-- The acceptance probability in the manuscript's ordering belongs to `[0,1]`. -/
theorem IsDensityOperator.trace_starProjection_probability
    {b : HilbertBasis κ ℂ E} {σ : E →L[ℂ] E} (hσ : IsDensityOperator b σ) :
    0 ≤ (operatorTrace b (σ * K.starProjection)).re ∧
      (operatorTrace b (σ * K.starProjection)).re ≤ 1 := by
  rw [← hσ.toIsPositiveTraceClass.operatorTrace_mul_comm K.starProjection]
  exact hσ.starProjection_probability K

end

end GaussianTesting.HilbertDensity
