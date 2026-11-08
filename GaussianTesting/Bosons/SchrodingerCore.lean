module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PolynomialGaussian
public import GaussianTesting.Bosons.FinitePolynomialCurve
public import GaussianTesting.Bosons.SchrodingerRotation
public import GaussianTesting.Bosons.SchrodingerAlgebra
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-! # The finite Gaussian core and its physical rotation derivative -/

namespace GaussianTesting

open MeasureTheory MvPolynomial
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- Substitution of the manuscript's real coordinate rotation into a polynomial. -/
def polynomialRotate (m : ℕ) (θ : ℝ) :
    MvPolynomial (Fin 2 × Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin 2 × Fin m) ℂ :=
  aeval (fun p => (Real.cos θ : ℂ) • X p + (Real.sin θ : ℂ) •
    (if p.1 = 0 then X (1, p.2) else -X (0, p.2)))

@[simp] theorem polynomialRotate_X (m : ℕ) (θ : ℝ) (p : Fin 2 × Fin m) :
    polynomialRotate m θ (X p) = (Real.cos θ : ℂ) • X p +
      (Real.sin θ : ℂ) • (if p.1 = 0 then X (1, p.2) else -X (0, p.2)) := by
  simp [polynomialRotate]

@[simp] theorem polynomialRotate_C (m : ℕ) (θ : ℝ) (c : ℂ) :
    polynomialRotate m θ (C c) = C c := by simp [polynomialRotate]

@[simp] theorem polynomialRotate_zero (m : ℕ) (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialRotate m 0 p = p := by
  have h : polynomialRotate m 0 = AlgHom.id ℂ _ := by
    ext i
    simp
  rw [h]
  rfl

/-- Polynomial substitution and actual coordinate rotation agree pointwise. -/
theorem polynomialRotate_eval (m : ℕ) (θ : ℝ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) (z : BosonConfig m) :
    eval (fun i => (z i : ℂ)) (polynomialRotate m θ p) =
      eval (fun i => (bosonRotate θ z i : ℂ)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    rcases i with ⟨i,j⟩
    fin_cases i <;> simp [polynomialRotate_X]
    ring

/-- Polynomial Gaussian realization intertwines the coordinate rotation with the
actual `L²` pullback. -/
theorem polynomialGaussian_rotate (m : ℕ) (θ : ℝ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialGaussian (polynomialRotate m θ p) =
      schrodingerRotation m θ (polynomialGaussian p) := by
  apply Lp.ext
  have h := (bosonRotation_measurePreserving m θ).quasiMeasurePreserving.ae
    (polynomialGaussian_coeFn p)
  filter_upwards [polynomialGaussian_coeFn (polynomialRotate m θ p),
    schrodingerRotation_coeFn m θ (polynomialGaussian p), h] with z hl hr hp
  rw [hl, hr, hp]
  simp only [polynomialGaussianFun, polynomialRotate_eval, norm_bosonRotate]

/-- The polynomial rotation orbit has a finite scalar expansion with the expected
infinitesimal derivative. -/
theorem polynomialRotate_hasFiniteCurveDeriv (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    HasFiniteCurveDeriv (fun θ => polynomialRotate m θ p)
      (polynomialRotationDeriv m p) 0 := by
  have hcos : HasDerivAt (fun θ : ℝ => (Real.cos θ : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp
  have hsin : HasDerivAt (fun θ : ℝ => (Real.sin θ : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).ofReal_comp
  have hX (i : Fin 2 × Fin m) :
      HasFiniteCurveDeriv (fun θ => polynomialRotate m θ (X i))
        (polynomialRotationDeriv m (X i)) 0 := by
    have hc := HasFiniteCurveDeriv.scalar _ _ (X i : MvPolynomial (Fin 2 × Fin m) ℂ) 0 hcos
    have hs := HasFiniteCurveDeriv.scalar _ _
      (if i.1 = 0 then X (1, i.2) else -X (0, i.2) : MvPolynomial (Fin 2 × Fin m) ℂ)
      0 hsin
    simpa [polynomialRotate_X, polynomialRotationDeriv, mkDerivation_X] using hc.add hs
  induction p using MvPolynomial.induction_on with
  | C c => simpa using HasFiniteCurveDeriv.const (C c : MvPolynomial (Fin 2 × Fin m) ℂ) 0
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    convert hp.mul (hX i) using 1
    · simp
    · rw [Derivation.leibniz]
      simp only [polynomialRotate_zero, smul_eq_mul]
      ring

/-- The actual `L²` orbit is differentiable at zero on the polynomial Gaussian core. -/
theorem hasDerivAt_schrodingerRotation_polynomialGaussian_zero (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    HasDerivAt (fun θ => schrodingerRotation m θ (polynomialGaussian p))
      ((-Complex.I) • polynomialGaussian (polynomialLambda m p)) 0 := by
  have h := (polynomialRotate_hasFiniteCurveDeriv m p).map polynomialGaussianLinear
  simpa only [polynomialGaussianLinear, LinearMap.coe_mk, AddHom.coe_mk,
    polynomialGaussian_rotate, polynomialRotationDeriv_eq, polynomialGaussian_smul] using h

/-- The physical orbit derivative at every angle on the polynomial Gaussian core. -/
theorem hasDerivAt_schrodingerRotation_polynomialGaussian (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) (t : ℝ) :
    HasDerivAt (fun θ => schrodingerRotation m θ (polynomialGaussian p))
      ((-Complex.I) • schrodingerRotation m t
        (polynomialGaussian (polynomialLambda m p))) t := by
  let U := (schrodingerRotation m t).toContinuousLinearEquiv.toContinuousLinearMap
  have h := (U.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_schrodingerRotation_polynomialGaussian_zero m p)
  have h' : HasDerivAt
      (fun s => schrodingerRotation m t (schrodingerRotation m s (polynomialGaussian p)))
      ((-Complex.I) • schrodingerRotation m t
        (polynomialGaussian (polynomialLambda m p))) (t - t) := by
    simpa [U, Function.comp_def] using h
  convert h'.comp_sub_const t t using 1
  funext s
  rw [← schrodingerRotation_add]
  have hangle : t + (s - t) = s := by ring
  rw [hangle]

/-- Ordered creation powers applied to the vacuum polynomial. The order is the
fixed enumeration supplied by `Fintype.equivFin`; no permutation of operators is
used in this definition. -/
def fockNumberPolynomialRaw {σ : Type*} [Fintype σ] (n : σ → ℕ) : MvPolynomial σ ℂ :=
  (List.finRange (Fintype.card σ)).foldr (fun i p =>
    (polynomialCreation ((Fintype.equivFin σ).symm i))^[n ((Fintype.equivFin σ).symm i)] p) 1

/-- The number-basis polynomial with the manuscript's factorial normalization
and the normalized `2m`-dimensional oscillator vacuum scalar. -/
def fockNumberPolynomial (m : ℕ) (n : (Fin 2 × Fin m) → ℕ) :
    MvPolynomial (Fin 2 × Fin m) ℂ :=
  ((Real.pi ^ (-(2 * m : ℝ) / 4) /
    Real.sqrt (∏ i, (Nat.factorial (n i) : ℝ)) : ℝ) : ℂ) • fockNumberPolynomialRaw n

/-- Polynomial factors of finite linear combinations of the specified Fock
number vectors, obtained from ordered creation powers on the vacuum. -/
def finiteFockPolynomialCore (m : ℕ) : Submodule ℂ (MvPolynomial (Fin 2 × Fin m) ℂ) :=
  Submodule.span ℂ (Set.range (fockNumberPolynomial m))

/-- The physical finite Fock graph: both coordinates are actual Lebesgue `L²`
wavefunctions and the second is the manuscript's creation-annihilation generator. -/
def schrodingerFiniteFockGraph (m : ℕ) :
    Submodule ℂ (SchrodingerSpace m × SchrodingerSpace m) :=
  LinearMap.range (((polynomialGaussianLinear (ι := Fin 2 × Fin m)).prod
    (polynomialGaussianLinear.comp (polynomialLambda m))).comp
      (finiteFockPolynomialCore m).subtype)

/-- Every pair in the specified finite Fock graph satisfies the analytic rotation
identity needed to pass to its graph closure. -/
theorem schrodingerFiniteFockGraph_hasDerivAt (m : ℕ)
    (z : SchrodingerSpace m × SchrodingerSpace m)
    (hz : z ∈ schrodingerFiniteFockGraph m) (t : ℝ) :
    HasDerivAt (fun θ => schrodingerRotation m θ z.1)
      ((-Complex.I) • schrodingerRotation m t z.2) t := by
  obtain ⟨p, rfl⟩ := hz
  exact hasDerivAt_schrodingerRotation_polynomialGaussian m p.1 t

end

end GaussianTesting
