module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.PerfectCompleteness
public import GaussianTesting.Fermions.GaussianSquareSpan
public import GaussianTesting.GradientFlow.Calculus

@[expose] public section

/-! # Optimality of the perfectly complete fermionic test -/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

/-- The fermionic accepting projection is the least positive contraction
accepting every Gaussian tensor square with probability one. The Gaussian
class includes both parities. -/
theorem fermionicTest_projection_le_effect (m : ℕ) {A : H2 (Qm m) →L[ℂ] H2 (Qm m)}
    (hA : 0 ≤ A) (hAnorm : ‖A‖ ≤ 1)
    (hcomplete : ∀ ψ ∈ fermionicGaussianStates m,
      (inner ℂ (tp2 ψ ψ) (A (tp2 ψ ψ))).re = 1) :
    (LinearMap.ker (lambdaF m)).starProjection ≤ A := by
  have h := closedSpan_projection_le_effect
    ((fun ψ => tp2 ψ ψ) '' fermionicGaussianStates m) hA hAnorm (by
      rintro _ ⟨ψ, hψ, rfl⟩
      rw [norm_tp2, ((mem_fermionicGaussianStates_iff ψ).mp hψ).norm_eq_one,
        one_mul, one_pow]
      exact hcomplete ψ hψ)
  change (fermionicGaussianSquareSpan m).topologicalClosure.starProjection ≤ A at h
  simpa only [fermionicGaussianSquareSpan_eq_kernel,
    (LinearMap.ker (lambdaF m)).closed_of_finiteDimensional.submodule_topologicalClosure_eq] using h

/-- Perfect completeness forces every other two-copy effect to accept at
least as often as `PF`, on every input vector and hence on identical copies. -/
theorem fermionicTest_acceptance_le (m : ℕ) {A : H2 (Qm m) →L[ℂ] H2 (Qm m)}
    (hA : 0 ≤ A) (hAnorm : ‖A‖ ≤ 1)
    (hcomplete : ∀ ψ ∈ fermionicGaussianStates m,
      (inner ℂ (tp2 ψ ψ) (A (tp2 ψ ψ))).re = 1) (y : H2 (Qm m)) :
    (inner ℂ y (PF m y)).re ≤ (inner ℂ y (A y)).re := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (sub_nonneg.mpr (fermionicTest_projection_le_effect m hA hAnorm hcomplete))
  have h := hp.re_inner_nonneg_right y
  change 0 ≤ (inner ℂ y ((A - (LinearMap.ker (lambdaF m)).starProjection) y)).re at h
  rw [sub_apply, inner_sub_right, Complex.sub_re] at h
  exact sub_nonneg.mp h

end
end GaussianTesting
