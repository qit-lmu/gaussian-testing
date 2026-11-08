module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.HilbertDensity
public import GaussianTesting.Bosons.BeamSplitter
public import GaussianTesting.GradientFlow.HilbertTensor

@[expose] public section

/-!
# Reduced density operators of bipartite pure states

The partial trace over the first factor is the Gram operator of the coordinate
columns. The bounded-observable identity below verifies its defining property
on the completed Hilbert tensor product. This supplies the reduced state used
in the manuscript's four-copy bosonic test.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι κ : Type*}

private theorem norm_colF_le (v : L2 (ι × κ)) (i : ι) : ‖colF v i‖ ≤ ‖v‖ := by
  have h : ‖colF v i‖ ^ 2 ≤ ∑' j, ‖colF v j‖ ^ 2 :=
    (colF_gramFam v).le_tsum i (fun j _ => sq_nonneg _)
  rw [colF_total] at h
  nlinarith [norm_nonneg (colF v i), norm_nonneg v]

/-- A fixed coordinate column as a continuous complex linear map. -/
def colCLM (i : ι) : L2 (ι × κ) →L[ℂ] L2 κ :=
  LinearMap.mkContinuous
    { toFun := fun v => colF v i
      map_add' := by
        intro u v
        apply lp.ext
        funext j
        rfl
      map_smul' := by
        intro z v
        apply lp.ext
        funext j
        rfl }
    1 (fun v => by simpa using norm_colF_le v i)

/-- The coordinate column with first-factor index `i`, viewed in the original
second Hilbert space. -/
def rightColumn (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (Φ : HilbertTensor E F) (i : ι) : F :=
  c.repr.symm (colF (hilbertCoords b.repr c.repr Φ) i)

/-- Taking a column is continuous and complex-linear in the bipartite vector. -/
def rightColumnCLM (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (i : ι) : HilbertTensor E F →L[ℂ] F :=
  c.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    colCLM i ∘L (hilbertCoords b.repr c.repr).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightColumnCLM_apply (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (i : ι) (Φ : HilbertTensor E F) :
    rightColumnCLM b c i Φ = rightColumn b c Φ i := rfl

@[simp] theorem rightColumn_tmul (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (x : E) (y : F) (i : ι) :
    rightColumn b c (hilbertTmul x y) i = b.repr x i • y := by
  rw [rightColumn, hilbertCoords_tmul]
  have h : colF (tpPair (b.repr x) (c.repr y)) i = b.repr x i • c.repr y := by
    apply lp.ext
    funext j
    rfl
  rw [h, map_smul, c.repr.symm_apply_apply]

theorem rightColumn_gramFam (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (Φ : HilbertTensor E F) : GramFam (rightColumn b c Φ) := by
  simpa only [GramFam, GaussianTesting.GramFam, rightColumn, c.repr.symm.norm_map]
    using colF_gramFam (hilbertCoords b.repr c.repr Φ)

theorem rightColumn_total (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (Φ : HilbertTensor E F) : (∑' i, ‖rightColumn b c Φ i‖ ^ 2) = ‖Φ‖ ^ 2 := by
  simp only [rightColumn, c.repr.symm.norm_map, colF_total,
    LinearIsometryEquiv.norm_map]

/-- Parseval's identity grouped by the first tensor factor. -/
theorem inner_eq_tsum_rightColumn (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (Φ Ψ : HilbertTensor E F) :
    inner ℂ Φ Ψ = ∑' i, inner ℂ (rightColumn b c Φ i) (rightColumn b c Ψ i) := by
  rw [← (hilbertCoords b.repr c.repr).inner_map_map Φ Ψ, lp.inner_eq_tsum,
    (lp.summable_inner (𝕜 := ℂ) _ _).tsum_prod]
  apply tsum_congr
  intro i
  simp only [rightColumn, c.repr.symm.inner_map_map, lp.inner_eq_tsum, colF_apply]

theorem rightColumn_tensorMap (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (B : F →L[ℂ] F) (Φ : HilbertTensor E F) (i : ι) :
    rightColumn b c (hilbertTensorMap (ContinuousLinearMap.id ℂ E) B Φ) i =
      B (rightColumn b c Φ i) := by
  have h : (rightColumnCLM b c i).comp
      (hilbertTensorMap (ContinuousLinearMap.id ℂ E) B) =
      B.comp (rightColumnCLM b c i) := by
    apply hilbertTensor_ext
    intro x y
    simp only [ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul,
      ContinuousLinearMap.id_apply, rightColumnCLM_apply, rightColumn_tmul, map_smul]
  exact DFunLike.congr_fun h Φ

variable [CompleteSpace F]

/-- The reduced operator obtained by tracing out the first tensor factor. -/
def reducedRight (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (Φ : HilbertTensor E F) : F →L[ℂ] F :=
  gramOp c (rightColumn b c Φ) (rightColumn_gramFam b c Φ)

theorem isPositiveTraceClass_reducedRight (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (Φ : HilbertTensor E F) :
    IsPositiveTraceClass c (reducedRight b c Φ) :=
  isPositiveTraceClass_gramOp c (rightColumn_gramFam b c Φ)

theorem positiveTrace_reducedRight (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (Φ : HilbertTensor E F) :
    positiveTrace c (reducedRight b c Φ) = ‖Φ‖ ^ 2 := by
  rw [reducedRight, positiveTrace_gramOp, rightColumn_total]

theorem isDensityOperator_reducedRight (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) {Φ : HilbertTensor E F} (hΦ : ‖Φ‖ = 1) :
    IsDensityOperator c (reducedRight b c Φ) :=
  ⟨isPositiveTraceClass_reducedRight b c Φ, by rw [positiveTrace_reducedRight, hΦ, one_pow]⟩

/-- The defining partial-trace identity, for every bounded observable. -/
theorem operatorTrace_mul_reducedRight (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (Φ : HilbertTensor E F) (B : F →L[ℂ] F) :
    operatorTrace c (B * reducedRight b c Φ) =
      inner ℂ Φ (hilbertTensorMap (ContinuousLinearMap.id ℂ E) B Φ) := by
  rw [reducedRight, operatorTrace_mul_gramOp, inner_eq_tsum_rightColumn b c]
  simp only [rightColumn_tensorMap]

/-- Rank-one observables recover every matrix coefficient of an operator. -/
theorem operatorTrace_rankOne_mul (c : HilbertBasis κ ℂ F) (A : F →L[ℂ] F)
    (x y : F) : operatorTrace c (InnerProductSpace.rankOne ℂ x y * A) =
      inner ℂ y (A x) := by
  unfold operatorTrace
  simp only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply, inner_smul_right]
  simp_rw [← A.adjoint_inner_left]
  rw [c.tsum_inner_mul_inner, A.adjoint_inner_left]

/-- The reduced operator is independent of both coordinate bases. -/
theorem reducedRight_basis {ι' κ' : Type*} (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (b' : HilbertBasis ι' ℂ E)
    (c' : HilbertBasis κ' ℂ F) (Φ : HilbertTensor E F) :
    reducedRight b c Φ = reducedRight b' c' Φ := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [← operatorTrace_rankOne_mul c _ x y,
    ← operatorTrace_rankOne_mul c' _ x y,
    operatorTrace_mul_reducedRight, operatorTrace_mul_reducedRight]

end

end GaussianTesting.HilbertDensity
