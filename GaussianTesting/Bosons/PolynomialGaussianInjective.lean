module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PolynomialGaussian
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! # Uniqueness of the polynomial factor of a Gaussian wavefunction -/

namespace GaussianTesting

open MeasureTheory MvPolynomial

noncomputable section

/-- Equality in Lebesgue `L²` of polynomial Gaussian vectors determines the
polynomial. Continuity first removes the null set; evaluation on real points
then determines the complex polynomial. -/
theorem polynomialGaussian_injective {ι : Type*} [Fintype ι] :
    Function.Injective (polynomialGaussian (ι := ι)) := by
  intro p q hpq
  have hae : polynomialGaussianFun p =ᵐ[volume] polynomialGaussianFun q :=
    (polynomialGaussian_coeFn p).symm.trans
      (hpq ▸ polynomialGaussian_coeFn q)
  have he := MeasureTheory.Measure.eq_of_ae_eq hae
    (polynomialGaussianFun_continuous p) (polynomialGaussianFun_continuous q)
  apply MvPolynomial.funext_set (fun _ => Set.range (Complex.ofReal : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro x hx
  choose y hy using fun i => hx i (Set.mem_univ i)
  have h := congrFun he (WithLp.toLp 2 y)
  simp only [polynomialGaussianFun, hy] at h
  exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) h

end
end GaussianTesting
