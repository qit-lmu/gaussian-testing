module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.OperatorTrace
public import Mathlib.Analysis.CStarAlgebra.Hom

@[expose] public section

/-!
# Density operators on arbitrary complex Hilbert spaces

An arbitrary Hilbert basis is used to define diagonal traces, with independence
of this choice proved below. Transport to ℓ² reuses the positive-square-root
Gram representation and the absolutely convergent bounded-observable trace.
No distinguished physical basis or Gram representation is assumed.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {κ ι : Type*}

/-- Coordinate transport of an operator in a Hilbert basis. -/
noncomputable def inBasis (b : HilbertBasis κ ℂ E) :
    (E →L[ℂ] E) ≃⋆ₐ[ℂ] (L2 κ →L[ℂ] L2 κ) := b.repr.conjStarAlgEquiv

@[simp] theorem inBasis_apply (b : HilbertBasis κ ℂ E) (A : E →L[ℂ] E)
    (x : L2 κ) : inBasis b A x = b.repr (A (b.repr.symm x)) := rfl

@[simp] theorem inBasis_norm (b : HilbertBasis κ ℂ E) (A : E →L[ℂ] E) :
    ‖inBasis b A‖ = ‖A‖ := NonUnitalStarAlgHom.norm_map (inBasis b) (inBasis b).injective A

/-- The positive diagonal trace in an explicitly specified Hilbert basis. -/
noncomputable def positiveTrace (b : HilbertBasis κ ℂ E) (ρ : E →L[ℂ] E) : ℝ :=
  ∑' i, (inner ℂ (b i) (ρ (b i))).re

/-- The complex diagonal trace; convergence is established for the products below. -/
noncomputable def operatorTrace (b : HilbertBasis κ ℂ E) (A : E →L[ℂ] E) : ℂ :=
  ∑' i, inner ℂ (b i) (A (b i))

/-- Positivity and the standard finite-diagonal criterion for trace class. -/
structure IsPositiveTraceClass (b : HilbertBasis κ ℂ E) (ρ : E →L[ℂ] E) : Prop where
  nonneg : 0 ≤ ρ
  summable_diagonal : Summable (fun i => (inner ℂ (b i) (ρ (b i))).re)

/-- A positive trace-class operator with trace one. -/
structure IsDensityOperator (b : HilbertBasis κ ℂ E) (ρ : E →L[ℂ] E) : Prop extends
    IsPositiveTraceClass b ρ where
  trace_eq_one : positiveTrace b ρ = 1

private theorem coordinate_diagonal (b : HilbertBasis κ ℂ E) (A : E →L[ℂ] E)
    (i : κ) : inner ℂ (l2HilbertBasis κ i) (inBasis b A (l2HilbertBasis κ i)) =
      inner ℂ (b i) (A (b i)) := by
  classical
  have hi : l2HilbertBasis κ i = b.repr (b i) := by
    rw [b.repr_self]
    rfl
  simp only [hi, inBasis_apply, b.repr.symm_apply_apply, b.repr.inner_map_map]

@[simp] theorem positiveTrace_inBasis (b : HilbertBasis κ ℂ E) (ρ : E →L[ℂ] E) :
    GaussianTesting.positiveTrace (inBasis b ρ) = positiveTrace b ρ := by
  simp only [GaussianTesting.positiveTrace, positiveTrace, coordinate_diagonal]

@[simp] theorem operatorTrace_inBasis (b : HilbertBasis κ ℂ E) (A : E →L[ℂ] E) :
    GaussianTesting.operatorTrace (inBasis b A) = operatorTrace b A := by
  simp only [GaussianTesting.operatorTrace, operatorTrace, coordinate_diagonal]

theorem isPositiveTraceClass_inBasis_iff (b : HilbertBasis κ ℂ E) (ρ : E →L[ℂ] E) :
    GaussianTesting.IsPositiveTraceClass (inBasis b ρ) ↔ IsPositiveTraceClass b ρ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using map_nonneg (inBasis b).symm h.nonneg
    · simpa only [coordinate_diagonal] using h.summable_diagonal
  · intro h
    exact ⟨map_nonneg (inBasis b) h.nonneg, by
      simpa only [coordinate_diagonal] using h.summable_diagonal⟩

theorem isDensityOperator_inBasis_iff (b : HilbertBasis κ ℂ E) (ρ : E →L[ℂ] E) :
    GaussianTesting.IsDensityOperator (inBasis b ρ) ↔ IsDensityOperator b ρ := by
  constructor
  · intro h
    exact ⟨(isPositiveTraceClass_inBasis_iff b ρ).mp h.toIsPositiveTraceClass,
      by simpa using h.trace_eq_one⟩
  · intro h
    exact ⟨(isPositiveTraceClass_inBasis_iff b ρ).mpr h.toIsPositiveTraceClass,
      by simpa using h.trace_eq_one⟩

/-- A second Hilbert basis, expressed in the coordinates of the first. -/
noncomputable def basisInBasis (b : HilbertBasis κ ℂ E) (c : HilbertBasis ι ℂ E) :
    HilbertBasis ι ℂ (L2 κ) := .ofRepr (b.repr.symm.trans c.repr)

omit [CompleteSpace E] in
@[simp] theorem basisInBasis_apply (b : HilbertBasis κ ℂ E) (c : HilbertBasis ι ℂ E)
    (i : ι) : basisInBasis b c i = b.repr (c i) := rfl

private theorem basisInBasis_diagonal (b : HilbertBasis κ ℂ E)
    (c : HilbertBasis ι ℂ E) (A : E →L[ℂ] E) (i : ι) :
    inner ℂ (basisInBasis b c i) (inBasis b A (basisInBasis b c i)) =
      inner ℂ (c i) (A (c i)) := by
  simp only [basisInBasis_apply, inBasis_apply, b.repr.symm_apply_apply,
    b.repr.inner_map_map]

theorem IsPositiveTraceClass.hasSum_diagonal {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) (c : HilbertBasis ι ℂ E) :
    HasSum (fun i => (inner ℂ (c i) (ρ (c i))).re) (positiveTrace b ρ) := by
  have h := (isPositiveTraceClass_inBasis_iff b ρ).mpr hρ
  simpa only [basisInBasis_diagonal, positiveTrace_inBasis] using
    h.hasSum_diagonal (basisInBasis b c)

/-- The trace-class criterion is independent of the Hilbert basis. -/
theorem isPositiveTraceClass_basis_iff (b : HilbertBasis κ ℂ E)
    (c : HilbertBasis ι ℂ E) (ρ : E →L[ℂ] E) :
    IsPositiveTraceClass b ρ ↔ IsPositiveTraceClass c ρ := by
  exact ⟨fun h => ⟨h.nonneg, (h.hasSum_diagonal c).summable⟩,
    fun h => ⟨h.nonneg, (h.hasSum_diagonal b).summable⟩⟩

theorem IsPositiveTraceClass.positiveTrace_basis {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) (c : HilbertBasis ι ℂ E) :
    positiveTrace c ρ = positiveTrace b ρ := (hρ.hasSum_diagonal c).tsum_eq

theorem isDensityOperator_basis_iff (b : HilbertBasis κ ℂ E)
    (c : HilbertBasis ι ℂ E) (ρ : E →L[ℂ] E) :
    IsDensityOperator b ρ ↔ IsDensityOperator c ρ := by
  constructor <;> intro h
  · exact ⟨(isPositiveTraceClass_basis_iff b c ρ).mp h.toIsPositiveTraceClass,
      (h.toIsPositiveTraceClass.positiveTrace_basis c).trans h.trace_eq_one⟩
  · exact ⟨(isPositiveTraceClass_basis_iff c b ρ).mp h.toIsPositiveTraceClass,
      (h.toIsPositiveTraceClass.positiveTrace_basis b).trans h.trace_eq_one⟩

/-- A summable family of vectors for a Gram representation. -/
def GramFam (g : ι → E) : Prop := Summable (fun i => ‖g i‖ ^ 2)

omit [CompleteSpace E] in
theorem GramFam.inBasis {g : ι → E} (hg : GramFam g) (b : HilbertBasis κ ℂ E) :
    GaussianTesting.GramFam (fun i => b.repr (g i)) := by
  simpa only [GaussianTesting.GramFam, GramFam, b.repr.norm_map] using hg

/-- The positive Gram operator, transported from coordinates. Its vector-series
formula below proves that this construction does not depend on the basis. -/
noncomputable def gramOp (b : HilbertBasis κ ℂ E) (g : ι → E) (hg : GramFam g) :
    E →L[ℂ] E :=
  (inBasis b).symm (GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b))

@[simp] theorem inBasis_gramOp (b : HilbertBasis κ ℂ E) (g : ι → E)
    (hg : GramFam g) : inBasis b (gramOp b g hg) =
      GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b) :=
  (inBasis b).apply_symm_apply _

theorem gramOp_hasSum (b : HilbertBasis κ ℂ E) {g : ι → E} (hg : GramFam g) (x : E) :
    HasSum (fun i => inner ℂ (g i) x • g i) (gramOp b g hg x) := by
  have h := ((hg.inBasis b).summable_coeff (b.repr x)).hasSum
  rw [← GaussianTesting.gramOp_apply] at h
  have h' := h.mapL b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun i => b.repr.symm
    (inner ℂ (b.repr (g i)) (b.repr x) • b.repr (g i)))
    (b.repr.symm (GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b)
      (b.repr x))) at h'
  simpa only [map_smul, b.repr.inner_map_map, b.repr.symm_apply_apply,
    gramOp, inBasis, LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply] using h'

theorem gramOp_apply (b : HilbertBasis κ ℂ E) {g : ι → E} (hg : GramFam g) (x : E) :
    gramOp b g hg x = ∑' i, inner ℂ (g i) x • g i := (gramOp_hasSum b hg x).tsum_eq.symm

theorem gramOp_basis (b : HilbertBasis κ ℂ E) (c : HilbertBasis ι ℂ E)
    {ν : Type*} {g : ν → E} (hg : GramFam g) : gramOp b g hg = gramOp c g hg := by
  ext x
  rw [gramOp_apply, gramOp_apply]

theorem isPositiveTraceClass_gramOp (b : HilbertBasis κ ℂ E) {g : ι → E}
    (hg : GramFam g) : IsPositiveTraceClass b (gramOp b g hg) := by
  apply (isPositiveTraceClass_inBasis_iff b _).mp
  rw [inBasis_gramOp]
  exact GaussianTesting.isPositiveTraceClass_gramOp (hg.inBasis b)

theorem positiveTrace_gramOp (b : HilbertBasis κ ℂ E) {g : ι → E} (hg : GramFam g) :
    positiveTrace b (gramOp b g hg) = ∑' i, ‖g i‖ ^ 2 := by
  rw [← positiveTrace_inBasis, inBasis_gramOp, GaussianTesting.positiveTrace_gramOp]
  simp only [b.repr.norm_map]

/-- The square-root Gram representation, transported back from ℓ². -/
theorem IsPositiveTraceClass.exists_gram_representation {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) :
    ∃ (g : κ → E) (hg : GramFam g),
      gramOp b g hg = ρ ∧ ∑' i, ‖g i‖ ^ 2 = positiveTrace b ρ := by
  obtain ⟨g, hg, hrep, hmass⟩ :=
    ((isPositiveTraceClass_inBasis_iff b ρ).mpr hρ).exists_gram_representation
  have hg' : GramFam (fun i => b.repr.symm (g i)) := by
    simpa only [GramFam, GaussianTesting.GramFam, b.repr.symm.norm_map] using hg
  refine ⟨_, hg', ?_, ?_⟩
  · have hc : inBasis b (gramOp b (fun i => b.repr.symm (g i)) hg') = inBasis b ρ := by
      rw [inBasis_gramOp]
      simpa only [b.repr.apply_symm_apply] using hrep
    exact (inBasis b).injective hc
  · simpa only [b.repr.symm.norm_map, positiveTrace_inBasis] using hmass

/-- Every positive trace-class operator of trace one admits a normalized
summable Gram representation on the original Hilbert space. -/
theorem IsDensityOperator.exists_normalized_gram_representation
    {b : HilbertBasis κ ℂ E} {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) :
    ∃ (g : κ → E) (hg : GramFam g),
      (∑' i, ‖g i‖ ^ 2) = 1 ∧ gramOp b g hg = ρ := by
  obtain ⟨g, hg, hrep, hmass⟩ := hρ.toIsPositiveTraceClass.exists_gram_representation
  exact ⟨g, hg, hmass.trans hρ.trace_eq_one, hrep⟩

theorem isDensityOperator_gramOp (b : HilbertBasis κ ℂ E) {g : ι → E} (hg : GramFam g)
    (hmass : ∑' i, ‖g i‖ ^ 2 = 1) : IsDensityOperator b (gramOp b g hg) :=
  ⟨isPositiveTraceClass_gramOp b hg, (positiveTrace_gramOp b hg).trans hmass⟩

/-- The complex trace of an observable is its absolutely convergent Gram expectation. -/
theorem operatorTrace_mul_gramOp (b : HilbertBasis κ ℂ E) {g : ι → E} (hg : GramFam g)
    (B : E →L[ℂ] E) :
    operatorTrace b (B * gramOp b g hg) = ∑' i, inner ℂ (g i) (B (g i)) := by
  rw [← operatorTrace_inBasis, map_mul, inBasis_gramOp,
    GaussianTesting.operatorTrace_mul_gramOp]
  simp only [GaussianTesting.complexTrPair, inBasis_apply, b.repr.symm_apply_apply,
    b.repr.inner_map_map]

theorem IsPositiveTraceClass.mul_hasSum_diagonal {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ)
    (B : E →L[ℂ] E) (c : HilbertBasis ι ℂ E) :
    HasSum (fun i => inner ℂ (c i) ((B * ρ) (c i))) (operatorTrace b (B * ρ)) := by
  have h := ((isPositiveTraceClass_inBasis_iff b ρ).mpr hρ).mul_hasSum_diagonal
    (inBasis b B) (basisInBasis b c)
  simpa only [← map_mul, basisInBasis_diagonal, operatorTrace_inBasis] using h

theorem IsPositiveTraceClass.mul_norm_summable_diagonal {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ)
    (B : E →L[ℂ] E) (c : HilbertBasis ι ℂ E) :
    Summable (fun i => ‖inner ℂ (c i) ((B * ρ) (c i))‖) :=
  (hρ.mul_hasSum_diagonal B c).summable.norm

theorem IsPositiveTraceClass.operatorTrace_basis {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ)
    (B : E →L[ℂ] E) (c : HilbertBasis ι ℂ E) :
    operatorTrace c (B * ρ) = operatorTrace b (B * ρ) :=
  (hρ.mul_hasSum_diagonal B c).tsum_eq

theorem IsPositiveTraceClass.operatorTrace_mul_comm {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) (B : E →L[ℂ] E) :
    operatorTrace b (B * ρ) = operatorTrace b (ρ * B) := by
  have h := ((isPositiveTraceClass_inBasis_iff b ρ).mpr hρ).operatorTrace_mul_comm
    (inBasis b B)
  simpa only [← map_mul, operatorTrace_inBasis] using h

theorem IsPositiveTraceClass.operatorTrace_eq_positiveTrace {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) :
    operatorTrace b ρ = (positiveTrace b ρ : ℂ) := by
  have h := ((isPositiveTraceClass_inBasis_iff b ρ).mpr hρ).operatorTrace_eq_positiveTrace
  simpa only [operatorTrace_inBasis, positiveTrace_inBasis] using h

/-- The bounded-observable trace estimate on any complex Hilbert space. -/
theorem IsPositiveTraceClass.norm_operatorTrace_mul_le {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) (B : E →L[ℂ] E) :
    ‖operatorTrace b (B * ρ)‖ ≤ ‖B‖ * positiveTrace b ρ := by
  have h := ((isPositiveTraceClass_inBasis_iff b ρ).mpr hρ).norm_operatorTrace_mul_le
    (inBasis b B)
  simpa only [← map_mul, operatorTrace_inBasis, positiveTrace_inBasis, inBasis_norm] using h

end GaussianTesting.HilbertDensity
