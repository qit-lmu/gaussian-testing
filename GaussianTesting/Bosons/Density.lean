module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GramRepresentation
public import GaussianTesting.Bosons.GramTrace

@[expose] public section

/-!
# Positive trace-class operators and density operators on ℓ²

For a positive bounded operator, the standard trace-class criterion is
summability of its diagonal in an orthonormal basis. Its trace is the sum of
that diagonal. We use the coordinate basis to make these definitions, then
prove that any Hilbert basis gives the same criterion and trace.

The Gram representation is a theorem, not part of the definition: the columns
of the positive square root give `ρ = ∑ |g i⟩⟨g i|`, and their total squared
norm is the trace. In particular every density operator has a normalized
summable Gram representation, as needed for Lemma 6.2. This file treats
positive trace-class operators; it does not define the trace of arbitrary
nonpositive operators.
-/

namespace GaussianTesting

variable {κ ι : Type*}

/-- The coordinate Hilbert basis of ℓ². -/
noncomputable def l2HilbertBasis (κ : Type*) : HilbertBasis κ ℂ (L2 κ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- A positive bounded operator is trace class when its nonnegative diagonal
is summable. `isPositiveTraceClass_iff_summable_diagonal` proves that this
criterion does not depend on the chosen Hilbert basis. -/
structure IsPositiveTraceClass (ρ : L2 κ →L[ℂ] L2 κ) : Prop where
  nonneg : 0 ≤ ρ
  summable_diagonal : Summable (fun i =>
    (inner ℂ (l2HilbertBasis κ i) (ρ (l2HilbertBasis κ i))).re)

/-- The diagonal trace, used here only for positive trace-class operators.
`IsPositiveTraceClass.hasSum_diagonal` identifies it in every Hilbert basis. -/
noncomputable def positiveTrace (ρ : L2 κ →L[ℂ] L2 κ) : ℝ :=
  ∑' i, (inner ℂ (l2HilbertBasis κ i) (ρ (l2HilbertBasis κ i))).re

/-- The manuscript's density operators: positive trace-class operators of trace one. -/
structure IsDensityOperator (ρ : L2 κ →L[ℂ] L2 κ) : Prop extends
    IsPositiveTraceClass ρ where
  trace_eq_one : positiveTrace ρ = 1

/-- The trace of a Gram operator is the total squared norm of its family. -/
theorem positiveTrace_gramOp {g : ι → L2 κ} (hg : GramFam g) :
    positiveTrace (gramOp g hg) = ∑' i, ‖g i‖ ^ 2 :=
  (gramOp_hasSum_diagonal hg (l2HilbertBasis κ)).tsum_eq

/-- Every summable Gram family defines a positive trace-class operator. -/
theorem isPositiveTraceClass_gramOp {g : ι → L2 κ} (hg : GramFam g) :
    IsPositiveTraceClass (gramOp g hg) := by
  refine ⟨?_, (gramOp_hasSum_diagonal hg (l2HilbertBasis κ)).summable⟩
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨gramOp_symmetric hg, fun x => ?_⟩
  change 0 ≤ (inner ℂ (gramOp g hg x) x).re
  rw [gramOp_symmetric hg]
  exact gramOp_nonneg hg x

/-- Construct the square-root Gram representation, with total mass equal to trace. -/
theorem IsPositiveTraceClass.exists_gram_representation
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsPositiveTraceClass ρ) :
    ∃ (g : κ → L2 κ) (hg : GramFam g),
      gramOp g hg = ρ ∧ ∑' i, ‖g i‖ ^ 2 = positiveTrace ρ := by
  refine ⟨sqrtGramFamily ρ (l2HilbertBasis κ),
    sqrtGramFamily_gramFam hρ.nonneg (l2HilbertBasis κ) hρ.summable_diagonal,
    gramOp_sqrtGramFamily hρ.nonneg (l2HilbertBasis κ) hρ.summable_diagonal, ?_⟩
  exact sqrtGramFamily_total hρ.nonneg (l2HilbertBasis κ)

/-- The positive trace has the same summable diagonal in every Hilbert basis. -/
theorem IsPositiveTraceClass.hasSum_diagonal
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsPositiveTraceClass ρ)
    (b : HilbertBasis ι ℂ (L2 κ)) :
    HasSum (fun i => (inner ℂ (b i) (ρ (b i))).re) (positiveTrace ρ) := by
  obtain ⟨g, hg, hrep, hmass⟩ := hρ.exists_gram_representation
  simpa only [hrep, hmass] using gramOp_hasSum_diagonal hg b

/-- For a positive operator, finite diagonal trace in any Hilbert basis is
equivalent to the trace-class definition using the coordinate basis. -/
theorem isPositiveTraceClass_iff_summable_diagonal
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : 0 ≤ ρ) (b : HilbertBasis ι ℂ (L2 κ)) :
    IsPositiveTraceClass ρ ↔
      Summable (fun i => (inner ℂ (b i) (ρ (b i))).re) := by
  constructor
  · intro h
    exact (h.hasSum_diagonal b).summable
  · intro hsum
    have hg := sqrtGramFamily_gramFam hρ b hsum
    have hrep := gramOp_sqrtGramFamily hρ b hsum
    rw [← hrep]
    exact isPositiveTraceClass_gramOp hg

/-- Density operators can be recognized by positivity and trace one in any
Hilbert basis, without a Gram representation as a hypothesis. -/
theorem isDensityOperator_iff_hasSum_diagonal
    (ρ : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι ℂ (L2 κ)) :
    IsDensityOperator ρ ↔
      0 ≤ ρ ∧ HasSum (fun i => (inner ℂ (b i) (ρ (b i))).re) 1 := by
  constructor
  · intro hρ
    refine ⟨hρ.nonneg, ?_⟩
    simpa only [hρ.trace_eq_one] using hρ.toIsPositiveTraceClass.hasSum_diagonal b
  · rintro ⟨hρ, htr⟩
    have hclass := (isPositiveTraceClass_iff_summable_diagonal hρ b).mpr htr.summable
    exact ⟨hclass, (hclass.hasSum_diagonal b).unique htr⟩

/-- Every density operator admits a normalized summable Gram representation.
No finite-rank or particular-purification hypothesis is required. -/
theorem IsDensityOperator.exists_normalized_gram_representation
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsDensityOperator ρ) :
    ∃ (g : κ → L2 κ) (hg : GramFam g),
      (∑' i, ‖g i‖ ^ 2) = 1 ∧ gramOp g hg = ρ := by
  obtain ⟨g, hg, hrep, hmass⟩ := hρ.toIsPositiveTraceClass.exists_gram_representation
  exact ⟨g, hg, hmass.trans hρ.trace_eq_one, hrep⟩

/-- Conversely, a normalized summable Gram family represents a density operator. -/
theorem isDensityOperator_gramOp {g : ι → L2 κ} (hg : GramFam g)
    (hmass : ∑' i, ‖g i‖ ^ 2 = 1) : IsDensityOperator (gramOp g hg) :=
  ⟨isPositiveTraceClass_gramOp hg, (positiveTrace_gramOp hg).trans hmass⟩

/-- The operator definition of density agrees with normalized Gram representations. -/
theorem isDensityOperator_iff_exists_gram_representation
    (ρ : L2 κ →L[ℂ] L2 κ) :
    IsDensityOperator ρ ↔ ∃ (g : κ → L2 κ) (hg : GramFam g),
      (∑' i, ‖g i‖ ^ 2) = 1 ∧ gramOp g hg = ρ := by
  constructor
  · exact IsDensityOperator.exists_normalized_gram_representation
  · rintro ⟨g, hg, hmass, rfl⟩
    exact isDensityOperator_gramOp hg hmass

end GaussianTesting
