module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.GradientFlow.HilbertTensorFour
public import GaussianTesting.Bosons.PartialTraceTensor

@[expose] public section

/-!
# The four-copy accepting projection

The construction applies the inverse two-copy unitary to registers 12 and 34,
groups the discarded registers 13 and retained registers 24, and measures the
two-copy projection on 24. This is the operator defined immediately before
Proposition 6.3 in the manuscript.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Tensor products preserve symmetry of bounded operators. -/
theorem hilbertTensorMap_symmetric (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (hB : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (x y : HilbertTensor E F) :
    inner ℂ (hilbertTensorMap A B x) y = inner ℂ x (hilbertTensorMap A B y) := by
  let T := hilbertTensorMap A B
  have h (x : HilbertTensor E F) : ∀ y, inner ℂ (T x) y = inner ℂ x (T y) := by
    refine hilbertTensor_induction (p := fun x => ∀ y,
      inner ℂ (T x) y = inner ℂ x (T y))
      (by
        have hc (y : HilbertTensor E F) :
            IsClosed {x | inner ℂ (T x) y = inner ℂ x (T y)} :=
          isClosed_eq (T.continuous.inner (𝕜 := ℂ) continuous_const)
            (continuous_id.inner (𝕜 := ℂ) continuous_const)
        simpa only [Set.ofPred_forall] using isClosed_iInter hc) ?_ ?_ x
    · intro u v y
      refine hilbertTensor_induction (p := fun y =>
        inner ℂ (T (hilbertTmul u v)) y = inner ℂ (hilbertTmul u v) (T y))
        (isClosed_eq (continuous_const.inner (𝕜 := ℂ) continuous_id)
          (continuous_const.inner (𝕜 := ℂ) T.continuous)) ?_ ?_ y
      · intro u' v'
        simp only [T, hilbertTensorMap_tmul, inner_hilbertTmul, hA, hB]
      · intro a b ha hb
        simp only [map_add, inner_add_right, ha, hb]
    · intro a b ha hb y
      simp only [map_add, inner_add_left, ha, hb]
  exact h x y

/-- Tensor products preserve idempotence of bounded operators. -/
theorem hilbertTensorMap_idempotent (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hA : ∀ x, A (A x) = A x) (hB : ∀ x, B (B x) = B x)
    (x : HilbertTensor E F) :
    hilbertTensorMap A B (hilbertTensorMap A B x) = hilbertTensorMap A B x := by
  have h : (hilbertTensorMap A B).comp (hilbertTensorMap A B) = hilbertTensorMap A B := by
    apply hilbertTensor_ext
    intro u v
    simp only [ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul, hA, hB]
  exact DFunLike.congr_fun h x

/-- Four copies, with the initial grouping into registers 12 and 34. -/
abbrev HilbertFourth (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  HilbertSquare (HilbertSquare E)

/-- Undo the two-copy unitary on each pair and regroup as registers 13 and 24. -/
def fourCopyPreparation (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E) :
    HilbertFourth E ≃ₗᵢ[ℂ] HilbertFourth E :=
  (hilbertTensorEquiv U.symm U.symm).trans hilbertReshuffle

/-- The accepting operator `U⊗² P₂₄ (U†)⊗²`, defined independently of a reduced
state or trace pairing. -/
def fourCopyProjection (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E)
    (P : HilbertSquare E →L[ℂ] HilbertSquare E) :
    HilbertFourth E →L[ℂ] HilbertFourth E :=
  (fourCopyPreparation U).symm.conjStarAlgEquiv
    (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare E)) P)

theorem fourCopyProjection_symmetric
    (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E)
    (P : HilbertSquare E →L[ℂ] HilbertSquare E)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (x y : HilbertFourth E) :
    inner ℂ (fourCopyProjection U P x) y = inner ℂ x (fourCopyProjection U P y) := by
  let V := fourCopyPreparation U
  let T := hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare E)) P
  have hT := hilbertTensorMap_symmetric (ContinuousLinearMap.id ℂ (HilbertSquare E))
    P (fun _ _ => rfl) hP (V x) (V y)
  change inner ℂ (V.symm (T (V x))) y = inner ℂ x (V.symm (T (V y)))
  rw [← V.inner_map_map (V.symm (T (V x))) y,
    ← V.inner_map_map x (V.symm (T (V y))),
    V.apply_symm_apply, V.apply_symm_apply]
  exact hT

theorem fourCopyProjection_idempotent
    (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E)
    (P : HilbertSquare E →L[ℂ] HilbertSquare E)
    (hP : ∀ x, P (P x) = P x) (x : HilbertFourth E) :
    fourCopyProjection U P (fourCopyProjection U P x) = fourCopyProjection U P x := by
  change (fourCopyPreparation U).symm
    (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare E)) P
      (fourCopyPreparation U ((fourCopyPreparation U).symm
        (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare E)) P
          (fourCopyPreparation U x))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,
    hilbertTensorMap_idempotent _ P (fun _ => rfl) hP]
  rfl

/-- The four-copy expectation after undoing the two-copy unitary. -/
theorem fourCopyProjection_expectation
    (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E)
    (P : HilbertSquare E →L[ℂ] HilbertSquare E) (x : HilbertFourth E) :
    inner ℂ x (fourCopyProjection U P x) =
      inner ℂ (fourCopyPreparation U x)
        (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare E)) P
          (fourCopyPreparation U x)) := by
  simpa only [fourCopyProjection, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply] using
    ((fourCopyPreparation U).inner_map_map x (fourCopyProjection U P x)).symm

/-- Identical pure inputs for the four-copy test. -/
def fourCopyInput (ψ : E) : HilbertFourth E :=
  hilbertTmul (hilbertTmul ψ ψ) (hilbertTmul ψ ψ)

@[simp] theorem fourCopyPreparation_input
    (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E) (ψ : E) :
    fourCopyPreparation U (fourCopyInput ψ) =
      hilbertReshuffle (hilbertTmul (U.symm (hilbertTmul ψ ψ))
        (U.symm (hilbertTmul ψ ψ))) := by
  simp only [fourCopyPreparation, fourCopyInput, LinearIsometryEquiv.trans_apply,
    hilbertTensorEquiv_tmul]

/-- Acceptance is the expectation of the independently constructed four-copy
operator on four identical copies. -/
def fourCopyAcceptance (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E)
    (P : HilbertSquare E →L[ℂ] HilbertSquare E) (ψ : E) : ℝ :=
  (inner ℂ (fourCopyInput ψ) (fourCopyProjection U P (fourCopyInput ψ))).re

variable [CompleteSpace E] {κ : Type*}

/-- The manuscript's reduced-state expression for the four-copy acceptance.
The left side is the Born expectation of an independently constructed operator;
the right side uses the partial trace of the actual prepared two-copy vector. -/
theorem fourCopyProjection_expectation_eq_reducedTrace (b : HilbertBasis κ ℂ E)
    (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E)
    (P : HilbertSquare E →L[ℂ] HilbertSquare E) (ψ : E) :
    inner ℂ (fourCopyInput ψ) (fourCopyProjection U P (fourCopyInput ψ)) =
      HilbertDensity.operatorTrace (HilbertDensity.tensorBasis b)
        (P * hilbertTensorMap
          (HilbertDensity.reducedRight b b (U.symm (hilbertTmul ψ ψ)))
          (HilbertDensity.reducedRight b b (U.symm (hilbertTmul ψ ψ)))) := by
  rw [fourCopyProjection_expectation, fourCopyPreparation_input,
    ← HilbertDensity.operatorTrace_mul_reducedRight
      (HilbertDensity.tensorBasis b) (HilbertDensity.tensorBasis b),
    HilbertDensity.reducedRight_reshuffle_square]

theorem fourCopyAcceptance_eq_reducedTrace (b : HilbertBasis κ ℂ E)
    (U : HilbertSquare E ≃ₗᵢ[ℂ] HilbertSquare E)
    (P : HilbertSquare E →L[ℂ] HilbertSquare E) (ψ : E) :
    fourCopyAcceptance U P ψ =
      (HilbertDensity.operatorTrace (HilbertDensity.tensorBasis b)
        (P * hilbertTensorMap
          (HilbertDensity.reducedRight b b (U.symm (hilbertTmul ψ ψ)))
          (HilbertDensity.reducedRight b b (U.symm (hilbertTmul ψ ψ))))).re :=
  congrArg Complex.re (fourCopyProjection_expectation_eq_reducedTrace b U P ψ)

end
end GaussianTesting
