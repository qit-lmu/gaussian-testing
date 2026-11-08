module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Density

@[expose] public section

/-!
# Complex traces against positive trace-class operators

The operator trace is defined by its coordinate diagonal. For products of a
bounded observable and a positive trace-class operator, the diagonal is
absolutely summable in every Hilbert basis and has the same sum. The trace
equals the Gram-family expectation, including for non-self-adjoint observables.
-/

namespace GaussianTesting

open scoped InnerProductSpace

set_option maxHeartbeats 1600000

variable {ι κ ι' : Type*}

/-- The diagonal trace. The results below establish its absolute convergence
and basis independence for bounded operators times positive trace-class operators. -/
noncomputable def operatorTrace (A : L2 κ →L[ℂ] L2 κ) : ℂ :=
  ∑' j, inner ℂ (l2HilbertBasis κ j) (A (l2HilbertBasis κ j))

/-- The complex expectation of a bounded operator in a Gram family. -/
noncomputable def complexTrPair (B : L2 κ →L[ℂ] L2 κ) (g : ι → L2 κ) : ℂ :=
  ∑' i, inner ℂ (g i) (B (g i))

theorem complexTrPair_norm_summable {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) :
    Summable (fun i => ‖inner ℂ (g i) (B (g i))‖) := by
  apply (hg.mul_left ‖B‖).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  calc
    _ ≤ ‖g i‖ * ‖B (g i)‖ := norm_inner_le_norm _ _
    _ ≤ ‖g i‖ * (‖B‖ * ‖g i‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
    _ = ‖B‖ * ‖g i‖ ^ 2 := by ring

theorem complexTrPair_summable {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) : Summable (fun i => inner ℂ (g i) (B (g i))) :=
  (complexTrPair_norm_summable hg B).of_norm

/-- The previous real pairing is the real part of the complex expectation. -/
theorem complexTrPair_re {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) : (complexTrPair B g).re = trPair B g :=
  Complex.re_tsum (complexTrPair_summable hg B)

private theorem gramFam_map {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) : GramFam (fun i => B (g i)) := by
  apply (hg.mul_left (‖B‖ ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro i
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm (g i)) 2

private theorem gram_basis_square_summable {g : ι → L2 κ} (hg : GramFam g)
    (b : HilbertBasis ι' ℂ (L2 κ)) :
    Summable (fun p : ι × ι' => ‖inner ℂ (g p.1) (b p.2)‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
  refine ⟨fun i => (hilbertBasis_hasSum_norm_inner_sq b (g i)).summable, ?_⟩
  simpa only [GramFam, (hilbertBasis_hasSum_norm_inner_sq b _).tsum_eq] using hg

private theorem gram_basis_product_norm_summable {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι' ℂ (L2 κ)) :
    Summable (fun p : ι × ι' =>
      ‖inner ℂ (g p.1) (b p.2) * inner ℂ (b p.2) (B (g p.1))‖) := by
  have h₁ := gram_basis_square_summable hg b
  have h₂ := gram_basis_square_summable (gramFam_map hg B) b
  apply ((h₁.add h₂).div_const 2).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  simp only [norm_mul, norm_inner_symm (b p.2) (B (g p.1))]
  nlinarith [sq_nonneg (‖inner ℂ (g p.1) (b p.2)‖ -
    ‖inner ℂ (B (g p.1)) (b p.2)‖)]

private theorem gram_basis_column_hasSum {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι' ℂ (L2 κ)) (j : ι') :
    HasSum (fun i => inner ℂ (g i) (b j) * inner ℂ (b j) (B (g i)))
      (inner ℂ (b j) ((B * gramOp g hg) (b j))) := by
  have h := ((hg.summable_coeff (b j)).hasSum.mapL B).mapL (innerSL ℂ (b j))
  simpa only [gramOp_apply, mul_apply_eq_comp, map_smul,
    innerSL_apply_apply, inner_smul_right, smul_eq_mul] using h

/-- The trace of an observable times a Gram operator in any Hilbert basis. -/
theorem mul_gramOp_hasSum_diagonal {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι' ℂ (L2 κ)) :
    HasSum (fun j => inner ℂ (b j) ((B * gramOp g hg) (b j)))
      (complexTrPair B g) := by
  have hd := (gram_basis_product_norm_summable hg B b).of_norm
  have hs := hd.prod_symm.prod.hasSum
  change HasSum (fun j => ∑' i, inner ℂ (g i) (b j) * inner ℂ (b j) (B (g i)))
    (∑' j, ∑' i, inner ℂ (g i) (b j) * inner ℂ (b j) (B (g i))) at hs
  have he : (∑' j, ∑' i, inner ℂ (g i) (b j) * inner ℂ (b j) (B (g i))) =
      complexTrPair B g := by
    rw [Summable.tsum_comm (f := fun i j =>
      inner ℂ (g i) (b j) * inner ℂ (b j) (B (g i))) hd]
    simp only [b.tsum_inner_mul_inner, complexTrPair]
  rw [he] at hs
  simpa only [(gram_basis_column_hasSum hg B b _).tsum_eq] using hs

/-- Operator trace agrees with the complex Gram-family expectation. -/
theorem operatorTrace_mul_gramOp {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) :
    operatorTrace (B * gramOp g hg) = complexTrPair B g :=
  (mul_gramOp_hasSum_diagonal hg B (l2HilbertBasis κ)).tsum_eq

/-- Absolute convergence of the observable diagonal in any Hilbert basis. -/
theorem mul_gramOp_norm_summable_diagonal {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι' ℂ (L2 κ)) :
    Summable (fun j => ‖inner ℂ (b j) ((B * gramOp g hg) (b j))‖) :=
  (mul_gramOp_hasSum_diagonal hg B b).summable.norm

private theorem complexTrPair_adjoint {g : ι → L2 κ}
    (B : L2 κ →L[ℂ] L2 κ) :
    star (complexTrPair B.adjoint g) = complexTrPair B g := by
  change (starRingEnd ℂ) (∑' i, inner ℂ (g i) (B.adjoint (g i))) = complexTrPair B g
  rw [Complex.conj_tsum, complexTrPair]
  apply tsum_congr
  intro i
  rw [B.adjoint_inner_right, inner_conj_symm]

/-- The opposite product has the same basis-independent diagonal sum. -/
theorem gramOp_mul_hasSum_diagonal {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι' ℂ (L2 κ)) :
    HasSum (fun j => inner ℂ (b j) ((gramOp g hg * B) (b j)))
      (complexTrPair B g) := by
  have h := (mul_gramOp_hasSum_diagonal hg B.adjoint b).star
  have hdiag (j : ι') :
      star (inner ℂ (b j) ((B.adjoint * gramOp g hg) (b j))) =
        inner ℂ (b j) ((gramOp g hg * B) (b j)) := by
    change (starRingEnd ℂ) (inner ℂ (b j) (B.adjoint (gramOp g hg (b j)))) = _
    rw [B.adjoint_inner_right, inner_conj_symm]
    change inner ℂ (gramOp g hg (b j)) (B (b j)) = _
    exact gramOp_symmetric hg (b j) (B (b j))
  simpa only [hdiag, complexTrPair_adjoint] using h

/-- Cyclic placement of the bounded observable in the trace. -/
theorem operatorTrace_gramOp_mul {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) :
    operatorTrace (gramOp g hg * B) = complexTrPair B g :=
  (gramOp_mul_hasSum_diagonal hg B (l2HilbertBasis κ)).tsum_eq

/-- Complex family-independence, without any restriction on the observable. -/
theorem complexTrPair_congr {g : ι → L2 κ} {g' : ι' → L2 κ}
    (hg : GramFam g) (hg' : GramFam g') (h : gramOp g hg = gramOp g' hg')
    (B : L2 κ →L[ℂ] L2 κ) : complexTrPair B g = complexTrPair B g' := by
  rw [← operatorTrace_mul_gramOp hg, ← operatorTrace_mul_gramOp hg', h]

/-- The observable trace is independent of the basis for every positive
trace-class operator, without choosing a Gram family in its statement. -/
theorem IsPositiveTraceClass.mul_hasSum_diagonal
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsPositiveTraceClass ρ)
    (B : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι ℂ (L2 κ)) :
    HasSum (fun i => inner ℂ (b i) ((B * ρ) (b i))) (operatorTrace (B * ρ)) := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  rw [operatorTrace_mul_gramOp hg]
  exact mul_gramOp_hasSum_diagonal hg B b

/-- The basis diagonal for a bounded observable times a positive trace-class
operator is absolutely summable. -/
theorem IsPositiveTraceClass.mul_norm_summable_diagonal
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsPositiveTraceClass ρ)
    (B : L2 κ →L[ℂ] L2 κ) (b : HilbertBasis ι ℂ (L2 κ)) :
    Summable (fun i => ‖inner ℂ (b i) ((B * ρ) (b i))‖) :=
  (hρ.mul_hasSum_diagonal B b).summable.norm

/-- Cyclicity for a bounded observable and a positive trace-class operator. -/
theorem IsPositiveTraceClass.operatorTrace_mul_comm
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsPositiveTraceClass ρ)
    (B : L2 κ →L[ℂ] L2 κ) : operatorTrace (B * ρ) = operatorTrace (ρ * B) := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  rw [operatorTrace_mul_gramOp hg, operatorTrace_gramOp_mul hg]

/-- The complex operator trace extends the previously defined positive trace. -/
theorem IsPositiveTraceClass.operatorTrace_eq_positiveTrace
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsPositiveTraceClass ρ) :
    operatorTrace ρ = (positiveTrace ρ : ℂ) := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  rw [positiveTrace_gramOp hg, ← one_mul (gramOp g hg), operatorTrace_mul_gramOp hg]
  simp only [complexTrPair, one_apply_eq_self, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow, Complex.ofReal_tsum]
  rfl

/-- The standard bound on a bounded-observable expectation in a Gram family. -/
theorem norm_complexTrPair_le {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) :
    ‖complexTrPair B g‖ ≤ ‖B‖ * ∑' i, ‖g i‖ ^ 2 := by
  calc
    _ ≤ ∑' i, ‖inner ℂ (g i) (B (g i))‖ :=
      norm_tsum_le_tsum_norm (complexTrPair_norm_summable hg B)
    _ ≤ ∑' i, ‖B‖ * ‖g i‖ ^ 2 := by
      apply (complexTrPair_norm_summable hg B).tsum_le_tsum _ (hg.mul_left ‖B‖)
      intro i
      calc
        _ ≤ ‖g i‖ * ‖B (g i)‖ := norm_inner_le_norm _ _
        _ ≤ ‖g i‖ * (‖B‖ * ‖g i‖) :=
          mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
        _ = ‖B‖ * ‖g i‖ ^ 2 := by ring
    _ = _ := tsum_mul_left

/-- `|Tr(Bρ)| ≤ ‖B‖ Tr(ρ)` for every positive trace-class operator. -/
theorem IsPositiveTraceClass.norm_operatorTrace_mul_le
    {ρ : L2 κ →L[ℂ] L2 κ} (hρ : IsPositiveTraceClass ρ)
    (B : L2 κ →L[ℂ] L2 κ) :
    ‖operatorTrace (B * ρ)‖ ≤ ‖B‖ * positiveTrace ρ := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  rw [operatorTrace_mul_gramOp hg, positiveTrace_gramOp hg]
  exact norm_complexTrPair_le hg B

end GaussianTesting
