module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PolynomialGaussian
public import GaussianTesting.Bosons.SchrodingerAlgebra
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Coordinate derivatives on the finite Schrödinger core

This identifies the polynomial-factor operators with the manuscript's actual
position and differential operators, rather than merely naming algebraic
operators after them.
-/

namespace GaussianTesting

open MvPolynomial

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A partial derivative of a polynomial evaluated on real coordinates. -/
theorem hasDerivAt_polynomial_eval_coordinate (p : MvPolynomial ι ℂ)
    (x : EuclideanSpace ℝ ι) (j : ι) :
    HasDerivAt (fun t : ℝ =>
      eval (fun i => ((x + t • EuclideanSpace.single j (1 : ℝ)) i : ℂ)) p)
      (eval (fun i => (x i : ℂ)) (pderiv j p)) 0 := by
  classical
  have hi (i : ι) : HasDerivAt
      (fun t : ℝ => ((x + t • EuclideanSpace.single j (1 : ℝ)) i : ℂ))
      (if i = j then 1 else 0) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (x i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (EuclideanSpace.single j (1 : ℝ) i))).ofReal_comp
      using 1
    · funext t
      simp [PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply, eq_comm]
    · by_cases h : i = j <;> simp [PiLp.single_apply, h]
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (0 : ℝ) c
  | add p q hp hq => simpa [Pi.add_def] using hp.add hq
  | mul_X p i hp =>
    convert hp.mul (hi i) using 1
    · simp [Pi.mul_def]
    · simp only [zero_smul, add_zero, pderiv_mul, map_add, map_mul, eval_X,
        pderiv_X, Pi.single_apply]
      split_ifs <;> simp_all [eq_comm]

/-- Differentiating a polynomial Gaussian produces exactly the polynomial
factor `∂ⱼP - XⱼP`, as used in the creation and annihilation definitions. -/
theorem hasDerivAt_polynomialGaussianFun_coordinate (p : MvPolynomial ι ℂ)
    (x : EuclideanSpace ℝ ι) (j : ι) :
    HasDerivAt (fun t : ℝ =>
      polynomialGaussianFun p (x + t • EuclideanSpace.single j (1 : ℝ)))
      (polynomialGaussianFun (gaussianPolynomialDeriv j p) x) 0 := by
  classical
  have hline : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) 0 := by
    simpa only [Pi.add_def, zero_add, one_smul, id_eq] using (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ)))
  have hnorm : HasDerivAt
      (fun t : ℝ => ‖x + t • EuclideanSpace.single j (1 : ℝ)‖ ^ 2) (2 * x j) 0 := by
    simpa [EuclideanSpace.inner_single_right] using hline.norm_sq
  have hgauss := (hnorm.neg.div_const 2).exp.ofReal_comp
  have hpoly := hasDerivAt_polynomial_eval_coordinate p x j
  convert hpoly.mul hgauss using 1
  · rfl
  · simp only [zero_smul, add_zero, polynomialGaussianFun, gaussianPolynomialDeriv,
      map_sub, map_mul, eval_X, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_neg, Complex.ofReal_ofNat, Pi.neg_apply]
    ring

/-- The annihilation operator is `(Xⱼ + ∂ⱼ)/√2` on the actual core wavefunctions. -/
theorem polynomialGaussianFun_annihilation (p : MvPolynomial ι ℂ)
    (x : EuclideanSpace ℝ ι) (j : ι) :
    polynomialGaussianFun (polynomialAnnihilation j p) x =
      (Real.sqrt 2 : ℂ)⁻¹ * ((x j : ℂ) * polynomialGaussianFun p x +
        deriv (fun t : ℝ => polynomialGaussianFun p
          (x + t • EuclideanSpace.single j (1 : ℝ))) 0) := by
  rw [(hasDerivAt_polynomialGaussianFun_coordinate p x j).deriv,
    polynomialAnnihilation_eq]
  simp [polynomialGaussianFun, gaussianPolynomialDeriv]
  ring

/-- The creation operator is `(Xⱼ - ∂ⱼ)/√2` on the actual core wavefunctions. -/
theorem polynomialGaussianFun_creation (p : MvPolynomial ι ℂ)
    (x : EuclideanSpace ℝ ι) (j : ι) :
    polynomialGaussianFun (polynomialCreation j p) x =
      (Real.sqrt 2 : ℂ)⁻¹ * ((x j : ℂ) * polynomialGaussianFun p x -
        deriv (fun t : ℝ => polynomialGaussianFun p
          (x + t • EuclideanSpace.single j (1 : ℝ))) 0) := by
  rw [(hasDerivAt_polynomialGaussianFun_coordinate p x j).deriv,
    polynomialCreation_eq]
  simp [polynomialGaussianFun, gaussianPolynomialDeriv]
  ring

end
end GaussianTesting
