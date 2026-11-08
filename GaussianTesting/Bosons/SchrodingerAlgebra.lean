module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Polynomial factors of the Schrödinger creation and annihilation operators

For a wavefunction `P(x) exp(-‖x‖²/2)`, differentiation replaces its polynomial
factor by `∂ⱼP - XⱼP`. Thus the manuscript's operators `(Xⱼ ± ∂ⱼ)/√2`
act on polynomial factors by `polynomialAnnihilation` and `polynomialCreation`.
The two-copy combination is precisely the infinitesimal coordinate rotation.
-/

namespace GaussianTesting

open MvPolynomial

noncomputable section

variable {σ : Type*}

/-- Polynomial factor after differentiating a polynomial times the vacuum Gaussian. -/
def gaussianPolynomialDeriv (j : σ) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  pderiv j P - X j * P

/-- Polynomial action of `(Xⱼ + ∂ⱼ)/√2` on Gaussian wavefunctions. -/
def polynomialAnnihilation (j : σ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (pderiv j).toLinearMap

/-- Polynomial action of `(Xⱼ - ∂ⱼ)/√2` on Gaussian wavefunctions. -/
def polynomialCreation (j : σ) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    ((2 : ℂ) • LinearMap.mulLeft ℂ (X j) - (pderiv j).toLinearMap)

@[simp] theorem polynomialAnnihilation_apply (j : σ) (P : MvPolynomial σ ℂ) :
    polynomialAnnihilation j P = ((Real.sqrt 2 : ℂ)⁻¹) • pderiv j P := rfl

@[simp] theorem polynomialCreation_apply (j : σ) (P : MvPolynomial σ ℂ) :
    polynomialCreation j P = ((Real.sqrt 2 : ℂ)⁻¹) •
      ((2 : ℂ) • (X j * P) - pderiv j P) := rfl

theorem polynomialAnnihilation_eq (j : σ) (P : MvPolynomial σ ℂ) :
    polynomialAnnihilation j P =
      ((Real.sqrt 2 : ℂ)⁻¹) • (X j * P + gaussianPolynomialDeriv j P) := by
  simp [polynomialAnnihilation, gaussianPolynomialDeriv]

theorem polynomialCreation_eq (j : σ) (P : MvPolynomial σ ℂ) :
    polynomialCreation j P =
      ((Real.sqrt 2 : ℂ)⁻¹) • (X j * P - gaussianPolynomialDeriv j P) := by
  rw [polynomialCreation_apply, gaussianPolynomialDeriv]
  congr 1
  module

private theorem inverse_sqrt_two_sq :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2 = 1 := by
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  field_simp
  simpa [pow_two] using hsq.symm

/-- Cancellation of the two mixed second derivatives in one pair of modes. -/
theorem polynomial_pair_generator {j k : σ} (hjk : j ≠ k)
    (P : MvPolynomial σ ℂ) :
    polynomialAnnihilation j (polynomialCreation k P) -
      polynomialCreation j (polynomialAnnihilation k P) =
        X k * pderiv j P - X j * pderiv k P := by
  classical
  have hkj : k ≠ j := Ne.symm hjk
  simp only [polynomialAnnihilation_apply, polynomialCreation_apply, map_smul, map_sub,
    pderiv_mul, pderiv_X_of_ne hkj, zero_mul, zero_add]
  calc
    _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2) •
        (X k * pderiv j P - X j * pderiv k P) := by module
    _ = _ := by rw [inverse_sqrt_two_sq, one_smul]

/-- The two-copy generator `i Σⱼ(aⱼ ⊗ aⱼ† - aⱼ† ⊗ aⱼ)` on polynomial factors. -/
def polynomialLambda (m : ℕ) :
    MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] MvPolynomial (Fin 2 × Fin m) ℂ :=
  Complex.I • ∑ j : Fin m,
    ((polynomialAnnihilation (0, j)).comp (polynomialCreation (1, j)) -
      (polynomialCreation (0, j)).comp (polynomialAnnihilation (1, j)))

/-- The manuscript generator equals `i Σⱼ(yⱼ ∂xⱼ - xⱼ ∂yⱼ)`; Gaussian
derivative terms cancel. This fixes the sign of the rotation. -/
theorem polynomialLambda_eq (m : ℕ) (P : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialLambda m P = Complex.I • ∑ j : Fin m,
      (X (1, j) * pderiv (0, j) P - X (0, j) * pderiv (1, j) P) := by
  simp only [polynomialLambda, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply polynomial_pair_generator
  simp

/-- The derivation induced by the infinitesimal coordinate rotation. -/
def polynomialRotationDeriv (m : ℕ) :
    Derivation ℂ (MvPolynomial (Fin 2 × Fin m) ℂ)
      (MvPolynomial (Fin 2 × Fin m) ℂ) :=
  mkDerivation ℂ (fun p => if p.1 = 0 then X (1, p.2) else -X (0, p.2))

theorem polynomialRotationDeriv_eq (m : ℕ) (P : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialRotationDeriv m P = (-Complex.I) • polynomialLambda m P := by
  classical
  have he : polynomialRotationDeriv m = ∑ j : Fin m,
      ((X (1, j) : MvPolynomial (Fin 2 × Fin m) ℂ) • pderiv (0, j) -
        (X (0, j) : MvPolynomial (Fin 2 × Fin m) ℂ) • pderiv (1, j)) := by
    apply derivation_ext
    rintro ⟨i, j⟩
    fin_cases i <;>
      simp [polynomialRotationDeriv, mkDerivation_X, pderiv_X, Pi.single_apply,
        Prod.ext_iff, eq_comm]
  rw [he, polynomialLambda_eq]
  simp only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  change DFunLike.coe (∑ j : Fin m,
      (X (1, j) • pderiv (0, j) - X (0, j) • pderiv (1, j))) P = _
  simp

end
end GaussianTesting
