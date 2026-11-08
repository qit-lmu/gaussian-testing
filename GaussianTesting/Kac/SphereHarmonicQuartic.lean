module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereMeasure
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-!
# The degree-four zonal harmonic polynomials

The three axis vectors in the spin-four case of Theorem 4.1 are realized on
the sphere by the restrictions of these homogeneous harmonic quartics.
Their restriction is the Legendre polynomial `(35 t^4 - 30 t^2 + 3) / 8`
in the corresponding coordinate. Only degree four is needed for sharpness.
-/

namespace GaussianTesting.SO3

open MvPolynomial

noncomputable section

/-- Squared Euclidean radius as a polynomial in the three real coordinates. -/
def sphereRadiusSquaredPolynomial : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, X i ^ 2

/-- Homogeneous degree-four extension of the zonal harmonic about axis `a`. -/
def zonalFourPolynomial (a : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  C (1 / 8 : ℝ) * (C 35 * X a ^ 4 -
    C 30 * (X a ^ 2 * sphereRadiusSquaredPolynomial) +
    C 3 * sphereRadiusSquaredPolynomial ^ 2)

private theorem radiusSquared_isHomogeneous : sphereRadiusSquaredPolynomial.IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_X_pow i 2

/-- These ambient zonal polynomials are homogeneous of degree four. -/
theorem zonalFourPolynomial_isHomogeneous (a : Fin 3) :
    (zonalFourPolynomial a).IsHomogeneous 4 := by
  exact ((((isHomogeneous_X_pow a 4).C_mul _).sub
    (((isHomogeneous_X_pow a 2).mul radiusSquared_isHomogeneous).C_mul _)).add
      ((radiusSquared_isHomogeneous.pow 2).C_mul _)).C_mul _

/-- The sum of the three second partial derivatives vanishes: the polynomial is harmonic. -/
theorem zonalFourPolynomial_laplacian (a : Fin 3) :
    ∑ i : Fin 3, pderiv i (pderiv i (zonalFourPolynomial a)) = 0 := by
  have hn (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
      pderiv i (ofNat(n) : MvPolynomial (Fin 3) ℝ) = 0 :=
    (pderiv i).map_natCast n
  fin_cases a <;>
    simp [zonalFourPolynomial, sphereRadiusSquaredPolynomial, Fin.sum_univ_three,
      hn, map_ofNat] <;> ring

/-- Restriction to the unit sphere gives the usual degree-four zonal formula. -/
theorem zonalFourPolynomial_eval_sphere (a : Fin 3) (x : Sphere) :
    eval (fun i => (x : SphereAmbient) i) (zonalFourPolynomial a) =
      (35 * (x : SphereAmbient) a ^ 4 - 30 * (x : SphereAmbient) a ^ 2 + 3) / 8 := by
  have hn : ‖(x : SphereAmbient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hr : eval (fun i => (x : SphereAmbient) i) sphereRadiusSquaredPolynomial = 1 := by
    have hs := congrArg (fun t : ℝ => t ^ 2) hn
    rw [EuclideanSpace.real_norm_sq_eq] at hs
    simpa only [sphereRadiusSquaredPolynomial, map_sum, eval_pow, eval_X, one_pow] using hs
  simp only [zonalFourPolynomial, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, hr]
  ring

end
end GaussianTesting.SO3
