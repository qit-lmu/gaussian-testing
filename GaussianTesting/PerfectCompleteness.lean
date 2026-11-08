module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.GradientFlow.Spectral
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

/-!
# Optimal tests with perfect completeness

Every positive contraction accepting all vectors in a set with certainty
dominates the orthogonal projection onto their closed linear span. Applying
this to Gaussian tensor squares gives the optimality assertion in Section 1.
For bosons the relevant span is the symmetric part of the kernel.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Saturating the acceptance bound of a contraction forces vector fixation. -/
theorem effect_fixes_of_acceptance_eq {A : H →L[ℂ] H} (hA : ‖A‖ ≤ 1)
    {x : H} (hx : (inner ℂ x (A x)).re = ‖x‖ ^ 2) : A x = x := by
  have hn : ‖A x‖ ≤ ‖x‖ :=
    (A.le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right hA (norm_nonneg x))
  have hs : ‖x - A x‖ ^ 2 = ‖x‖ ^ 2 -
      2 * (inner ℂ x (A x)).re + ‖A x‖ ^ 2 := by
    rw [@norm_sub_sq ℂ]
    rfl
  rw [hx] at hs
  have hz : ‖x - A x‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖x - A x‖, pow_le_pow_left₀ (norm_nonneg (A x)) hn 2]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm

omit [CompleteSpace H] in
/-- An effect fixing the generating vectors fixes their closed linear span. -/
theorem effect_fixes_closedSpan {A : H →L[ℂ] H} {S : Set H}
    (hS : ∀ x ∈ S, A x = x) {x : H}
    (hx : x ∈ (Submodule.span ℂ S).topologicalClosure) : A x = x := by
  have hspan : Submodule.span ℂ S ≤
      (A - ContinuousLinearMap.id ℂ H).ker := by
    apply Submodule.span_le.mpr
    intro y hy
    change A y - y = 0
    exact sub_eq_zero.mpr (hS y hy)
  have hclosed := (Submodule.span ℂ S).topologicalClosure_minimal hspan
    (A - ContinuousLinearMap.id ℂ H).isClosed_ker
  have hz := hclosed hx
  change A x - x = 0 at hz
  exact sub_eq_zero.mp hz

/-- A positive operator fixing a closed subspace dominates its orthogonal
projection. -/
theorem starProjection_le_of_fixes (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    {A : H →L[ℂ] H} (hA : 0 ≤ A) (hfix : ∀ x ∈ M, A x = x) :
    M.starProjection ≤ A := by
  let P := M.starProjection
  have hAP : A * P = P := by
    ext x
    exact hfix (P x) (M.starProjection_apply_mem x)
  have hP : star P = P := (isSelfAdjoint_starProjection M).star_eq
  have hAs : star A = A := (IsSelfAdjoint.of_nonneg hA).star_eq
  have hPA : P * A = P := by
    have h := congrArg star hAP
    simpa only [star_mul, hP, hAs] using h
  have hPP : P * P = P := M.isIdempotentElem_starProjection
  have he : (1 - P) * A * (1 - P) = A - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPA, hAP, hPP]
    abel
  have hn := star_left_conjugate_nonneg hA (1 - P)
  rw [star_sub, star_one, hP, he] at hn
  exact sub_nonneg.mp hn

/-- The projection onto the closed span is the least accepting effect with
perfect completeness on the given family. -/
theorem closedSpan_projection_le_effect (S : Set H) {A : H →L[ℂ] H}
    (hA : 0 ≤ A) (hAnorm : ‖A‖ ≤ 1)
    (hcomplete : ∀ x ∈ S, (inner ℂ x (A x)).re = ‖x‖ ^ 2) :
    (Submodule.span ℂ S).topologicalClosure.starProjection ≤ A := by
  apply starProjection_le_of_fixes _ hA
  intro x hx
  exact effect_fixes_closedSpan
    (fun y hy => effect_fixes_of_acceptance_eq hAnorm (hcomplete y hy)) hx

/-- Consequently the span projection minimizes acceptance on every input. -/
theorem closedSpan_acceptance_le (S : Set H) {A : H →L[ℂ] H}
    (hA : 0 ≤ A) (hAnorm : ‖A‖ ≤ 1)
    (hcomplete : ∀ x ∈ S, (inner ℂ x (A x)).re = ‖x‖ ^ 2) (y : H) :
    (inner ℂ y ((Submodule.span ℂ S).topologicalClosure.starProjection y)).re ≤
      (inner ℂ y (A y)).re := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (sub_nonneg.mpr (closedSpan_projection_le_effect S hA hAnorm hcomplete))
  have h := hp.re_inner_nonneg_right y
  change 0 ≤ (inner ℂ y ((A -
    (Submodule.span ℂ S).topologicalClosure.starProjection) y)).re at h
  rw [sub_apply, inner_sub_right, Complex.sub_re] at h
  exact sub_nonneg.mp h

end
end GaussianTesting
