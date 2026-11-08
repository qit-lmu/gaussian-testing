module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.CopyPolynomialCoordinates
public import GaussianTesting.Bosons.BalancedPolynomialGeneration

@[expose] public section

/-! # Polynomial invariants of physical two-copy rotations and swap -/

namespace GaussianTesting

noncomputable section

/-- A polynomial in the kernel of the physical copy generator and fixed by
the physical quarter turn and swap is a polynomial in the Gram entries.
The two-copy rotation average supplies the first two hypotheses. -/
theorem polynomial_mem_copyGramAlgebra_of_invariant {m : ℕ}
    (p : MvPolynomial (Fin 2 × Fin m) ℂ)
    (hΛ : polynomialLambda m p = 0)
    (hquarter : polynomialRotate m (Real.pi / 2) p = p)
    (hswap : copyModeSwap m p = p) : p ∈ copyGramAlgebra m := by
  have hcomplex := mem_symmetricMixedAlgebra_of_balanced_swap
    (realCopyToComplex m p) (realCopyToComplex_balanced p hΛ)
    (realCopyToComplex_swap p hquarter hswap)
  simpa only [complexCopyToReal_realCopyToComplex] using
    complexCopyToReal_mem_copyGramAlgebra hcomplex

end
end GaussianTesting
