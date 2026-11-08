module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Mixed
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

@[expose] public section

/-!
# Square-root Gram representations of positive operators

For a positive bounded operator `ρ`, the images of an orthonormal basis under
its positive square root form a Gram representation. Summability of the basis
diagonal is exactly summability of the squared norms of this family. This is
the representation step needed to apply the Gram-family form of Lemma 6.2.
-/

namespace GaussianTesting

set_option maxSynthPendingDepth 5

open scoped InnerProductSpace

variable {ι κ : Type*}

local instance : NonUnitalContinuousFunctionalCalculus ℝ (L2 κ →L[ℂ] L2 κ) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

/-- The columns of the positive square root in a Hilbert basis. -/
noncomputable def sqrtGramFamily (ρ : L2 κ →L[ℂ] L2 κ)
    (b : HilbertBasis ι ℂ (L2 κ)) : ι → L2 κ :=
  fun i => CFC.sqrt ρ (b i)

/-- Each squared column norm is the corresponding diagonal coefficient. -/
theorem norm_sq_sqrtGramFamily_eq_diagonal {ρ : L2 κ →L[ℂ] L2 κ}
    (hρ : 0 ≤ ρ) (b : HilbertBasis ι ℂ (L2 κ)) (i : ι) :
    ‖sqrtGramFamily ρ b i‖ ^ 2 = (inner ℂ (b i) (ρ (b i))).re := by
  have hs (x y : L2 κ) : inner ℂ (CFC.sqrt ρ x) y = inner ℂ x (CFC.sqrt ρ y) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)).isSymmetric x y
  have hsq : CFC.sqrt ρ (CFC.sqrt ρ (b i)) = ρ (b i) :=
    DFunLike.congr_fun (CFC.sqrt_mul_sqrt_self ρ hρ) (b i)
  rw [sqrtGramFamily, norm_sq_eq_re_inner (𝕜 := ℂ), hs, hsq]
  rfl

/-- Summability of the positive diagonal gives a summable Gram family. -/
theorem sqrtGramFamily_gramFam {ρ : L2 κ →L[ℂ] L2 κ}
    (hρ : 0 ≤ ρ) (b : HilbertBasis ι ℂ (L2 κ))
    (hsum : Summable (fun i => (inner ℂ (b i) (ρ (b i))).re)) :
    GramFam (sqrtGramFamily ρ b) := by
  simpa only [GramFam, norm_sq_sqrtGramFamily_eq_diagonal hρ b] using hsum

/-- The mass of the square-root family equals the sum of the positive diagonal. -/
theorem sqrtGramFamily_total {ρ : L2 κ →L[ℂ] L2 κ}
    (hρ : 0 ≤ ρ) (b : HilbertBasis ι ℂ (L2 κ)) :
    ∑' i, ‖sqrtGramFamily ρ b i‖ ^ 2 =
      ∑' i, (inner ℂ (b i) (ρ (b i))).re := by
  exact tsum_congr (norm_sq_sqrtGramFamily_eq_diagonal hρ b)

/-- Parseval's identity identifies the Gram operator with the original operator. -/
theorem gramOp_sqrtGramFamily {ρ : L2 κ →L[ℂ] L2 κ}
    (hρ : 0 ≤ ρ) (b : HilbertBasis ι ℂ (L2 κ))
    (hsum : Summable (fun i => (inner ℂ (b i) (ρ (b i))).re)) :
    gramOp (sqrtGramFamily ρ b) (sqrtGramFamily_gramFam hρ b hsum) = ρ := by
  have hs (x y : L2 κ) : inner ℂ (CFC.sqrt ρ x) y = inner ℂ x (CFC.sqrt ρ y) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)).isSymmetric x y
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [inner_gramOp]
  simp only [sqrtGramFamily, ← hs x, hs _ y]
  rw [b.tsum_inner_mul_inner, hs]
  exact congrArg (inner ℂ x) (DFunLike.congr_fun (CFC.sqrt_mul_sqrt_self ρ hρ) y)

end GaussianTesting
