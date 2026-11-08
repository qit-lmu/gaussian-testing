module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PartialTrace
public import GaussianTesting.Bosons.SignedSwapPurity
public import GaussianTesting.GradientFlow.HilbertTensorFour

@[expose] public section

/-!
# Partial trace and the four-copy regrouping

Regrouping two copies of a bipartite pure state yields the tensor square of its
reduced state, as required in the four-copy bosonic acceptance formula.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι κ : Type*}

/-- Columns factor under the `(12)(34)` to `(13)(24)` regrouping. -/
theorem rightColumn_reshuffle_tmul (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (Φ Ψ : HilbertTensor E F) (i j : ι) :
    rightColumn (tensorBasis b) (tensorBasis c)
        (hilbertReshuffle (hilbertTmul Φ Ψ)) (i, j) =
      hilbertTmul (rightColumn b c Φ i) (rightColumn b c Ψ j) := by
  have h : (rightColumnCLM (tensorBasis b) (tensorBasis c) (i, j)).comp
      (hilbertReshuffle (E := E) (F := F) (G := E) (K := F)).toLinearIsometry.toContinuousLinearMap =
      hilbertTensorMap (rightColumnCLM b c i) (rightColumnCLM b c j) := by
    apply hilbertTensorFour_ext
    intro x y z w
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, hilbertReshuffle_tmul,
      rightColumnCLM_apply, rightColumn_tmul, hilbertTensorMap_tmul]
    change (hilbertCoords b.repr b.repr (hilbertTmul x z)) (i, j) •
      hilbertTmul y w = hilbertTmul (b.repr x i • y) (b.repr z j • w)
    simp only [hilbertCoords_tmul, tpPair_apply, map_smul,
      smul_apply, smul_smul, mul_comm]
  exact (DFunLike.congr_fun h (hilbertTmul Φ Ψ)).trans
    (hilbertTensorMap_tmul _ _ _ _)

variable [CompleteSpace F]

/-- The reduced operator on copies 2 and 4 is the tensor square of the
one-pair reduced operator. -/
theorem reducedRight_reshuffle_square (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ F) (Φ : HilbertTensor E F) :
    reducedRight (tensorBasis b) (tensorBasis c)
        (hilbertReshuffle (hilbertTmul Φ Φ)) =
      hilbertTensorMap (reducedRight b c Φ) (reducedRight b c Φ) := by
  have h : rightColumn (tensorBasis b) (tensorBasis c)
      (hilbertReshuffle (hilbertTmul Φ Φ)) =
      fun p : ι × ι => hilbertTmul (rightColumn b c Φ p.1) (rightColumn b c Φ p.2) := by
    funext p
    exact rightColumn_reshuffle_tmul b c Φ Φ p.1 p.2
  unfold reducedRight
  rw [← gramOp_tensor c (rightColumn_gramFam b c Φ)]
  ext x
  simp only [gramOp_apply, h]

end

end GaussianTesting.HilbertDensity
