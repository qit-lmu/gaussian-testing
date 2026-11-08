module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Algebra of the difference of two pure-state projections

These identities are the rank-two computation used for the trace-distance
identity after Theorem 1.1. They hold in an arbitrary complex Hilbert space.
-/

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The difference `|ψ⟩⟨ψ| − |φ⟩⟨φ|` of the two pure-state operators. -/
def pureStateDifference (ψ φ : E) : E →L[ℂ] E :=
  InnerProductSpace.rankOne ℂ ψ ψ - InnerProductSpace.rankOne ℂ φ φ

theorem pureStateDifference_isSelfAdjoint (ψ φ : E) :
    IsSelfAdjoint (pureStateDifference ψ φ) := by
  simp [IsSelfAdjoint, pureStateDifference, ContinuousLinearMap.star_eq_adjoint]

theorem pureStateDifference_sq_nonneg (ψ φ : E) :
    0 ≤ pureStateDifference ψ φ ^ 2 := by
  simpa only [sq, (pureStateDifference_isSelfAdjoint ψ φ).star_eq] using
    star_mul_self_nonneg (pureStateDifference ψ φ)

omit [CompleteSpace E] in
private theorem rankOne_mul (x y z w : E) :
    InnerProductSpace.rankOne ℂ x y * InnerProductSpace.rankOne ℂ z w =
      inner ℂ y z • InnerProductSpace.rankOne ℂ x w :=
  InnerProductSpace.rankOne_comp_rankOne x y z w

omit [CompleteSpace E] in
/-- The square is a sum of four rank-one operators. -/
theorem pureStateDifference_sq (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    pureStateDifference ψ φ ^ 2 =
      InnerProductSpace.rankOne ℂ ψ ψ + InnerProductSpace.rankOne ℂ φ φ -
        inner ℂ ψ φ • InnerProductSpace.rankOne ℂ ψ φ -
        inner ℂ φ ψ • InnerProductSpace.rankOne ℂ φ ψ := by
  have hiψ : inner ℂ ψ ψ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have hiφ : inner ℂ φ φ = 1 := by simp [inner_self_eq_norm_sq_to_K, hφ]
  simp only [pureStateDifference, sq, sub_mul, mul_sub, rankOne_mul, hiψ, hiφ, one_smul]
  abel

omit [CompleteSpace E] in
/-- The cubic relation records the two possible nonzero eigenvalues. -/
theorem pureStateDifference_cube (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    pureStateDifference ψ φ ^ 3 =
      (1 - ‖inner ℂ ψ φ‖ ^ 2 : ℝ) • pureStateDifference ψ φ := by
  let P := InnerProductSpace.rankOne ℂ ψ ψ
  let Q := InnerProductSpace.rankOne ℂ φ φ
  have hPP : P * P = P := InnerProductSpace.isIdempotentElem_rankOne_self hψ
  have hQQ : Q * Q = Q := InnerProductSpace.isIdempotentElem_rankOne_self hφ
  have hnorm : inner ℂ ψ φ * inner ℂ φ ψ = (‖inner ℂ ψ φ‖ ^ 2 : ℝ) := by
    rw [← inner_conj_symm φ ψ]
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' (inner ℂ ψ φ)
  have hPQP : P * Q * P = (‖inner ℂ ψ φ‖ ^ 2 : ℝ) • P := by
    dsimp [P, Q]
    rw [rankOne_mul, smul_mul_assoc, rankOne_mul, smul_smul, hnorm]
    exact IsScalarTower.algebraMap_smul ℂ (‖inner ℂ ψ φ‖ ^ 2 : ℝ)
      (InnerProductSpace.rankOne ℂ ψ ψ)
  have hQPQ : Q * P * Q = (‖inner ℂ ψ φ‖ ^ 2 : ℝ) • Q := by
    dsimp [P, Q]
    rw [rankOne_mul, smul_mul_assoc, rankOne_mul, smul_smul, mul_comm, hnorm]
    exact IsScalarTower.algebraMap_smul ℂ (‖inner ℂ ψ φ‖ ^ 2 : ℝ)
      (InnerProductSpace.rankOne ℂ φ φ)
  change (P - Q) ^ 3 = _
  have he : (P - Q) ^ 3 = P - Q - P * Q * P + Q * P * Q := by
    noncomm_ring [hPP, hQQ]
  rw [he, hPQP, hQPQ]
  change P - Q - (‖inner ℂ ψ φ‖ ^ 2 : ℝ) • P + (‖inner ℂ ψ φ‖ ^ 2 : ℝ) • Q =
    (1 - ‖inner ℂ ψ φ‖ ^ 2 : ℝ) • (P - Q)
  module

omit [CompleteSpace E] in
/-- Squaring the square gives the relation used to identify the positive square root. -/
theorem pureStateDifference_fourth (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    pureStateDifference ψ φ ^ 4 =
      (1 - ‖inner ℂ ψ φ‖ ^ 2 : ℝ) • (pureStateDifference ψ φ ^ 2) := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ, pureStateDifference_cube ψ φ hψ hφ,
    smul_mul_assoc, ← sq]

/-- At overlap one the two pure-state projections coincide, including different phases. -/
theorem pureStateDifference_eq_zero_of_overlap_sq_eq_one (ψ φ : E)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (h : ‖inner ℂ ψ φ‖ ^ 2 = 1) :
    pureStateDifference ψ φ = 0 := by
  have h4 := pureStateDifference_fourth ψ φ hψ hφ
  rw [h, sub_self, zero_smul] at h4
  have h2 : pureStateDifference ψ φ ^ 2 = 0 := by
    apply star_mul_self_eq_zero.mp
    rw [((pureStateDifference_isSelfAdjoint ψ φ).pow 2).star_eq, ← pow_add]
    exact h4
  apply star_mul_self_eq_zero.mp
  rw [(pureStateDifference_isSelfAdjoint ψ φ).star_eq, ← sq]
  exact h2

end
end GaussianTesting
