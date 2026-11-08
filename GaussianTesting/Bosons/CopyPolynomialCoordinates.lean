module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.BalancedQuadratic
public import GaussianTesting.Bosons.SchrodingerCore

@[expose] public section

/-! # Complex coordinates for the two-copy polynomial rotation action -/

namespace GaussianTesting

open MvPolynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Substitute `u = x + iy` and `v = x - iy`. -/
def complexCopyToReal (m : ℕ) :
    MvPolynomial (Fin 2 × Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin 2 × Fin m) ℂ :=
  aeval (fun ai => if ai.1 = 0 then X (0, ai.2) + Complex.I • X (1, ai.2)
    else X (0, ai.2) - Complex.I • X (1, ai.2))

/-- Substitute `x = (u + v)/2` and `y = -i(u-v)/2`. -/
def realCopyToComplex (m : ℕ) :
    MvPolynomial (Fin 2 × Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin 2 × Fin m) ℂ :=
  aeval (fun ai => if ai.1 = 0 then (2 : ℂ)⁻¹ • (X (0, ai.2) + X (1, ai.2))
    else (-Complex.I) • ((2 : ℂ)⁻¹ • (X (0, ai.2) - X (1, ai.2))))

@[simp] theorem complexCopyToReal_X_zero (m : ℕ) (j : Fin m) :
    complexCopyToReal m (X (0, j)) = X (0, j) + Complex.I • X (1, j) := by
  simp [complexCopyToReal]

@[simp] theorem complexCopyToReal_X_one (m : ℕ) (j : Fin m) :
    complexCopyToReal m (X (1, j)) = X (0, j) - Complex.I • X (1, j) := by
  simp [complexCopyToReal]

@[simp] theorem realCopyToComplex_X_zero (m : ℕ) (j : Fin m) :
    realCopyToComplex m (X (0, j)) = (2 : ℂ)⁻¹ • (X (0, j) + X (1, j)) := by
  simp [realCopyToComplex]

@[simp] theorem realCopyToComplex_X_one (m : ℕ) (j : Fin m) :
    realCopyToComplex m (X (1, j)) =
      (-Complex.I) • ((2 : ℂ)⁻¹ • (X (0, j) - X (1, j))) := by
  simp [realCopyToComplex]

theorem complexCopyToReal_realCopyToComplex (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    complexCopyToReal m (realCopyToComplex m p) = p := by
  have h : (complexCopyToReal m).comp (realCopyToComplex m) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a,j⟩
    fin_cases a
    · change complexCopyToReal m (realCopyToComplex m (X (0,j))) = X (0,j)
      rw [realCopyToComplex_X_zero, map_smul, map_add, complexCopyToReal_X_zero,
        complexCopyToReal_X_one]
      module
    · change complexCopyToReal m (realCopyToComplex m (X (1,j))) = X (1,j)
      rw [realCopyToComplex_X_one, map_smul, map_smul, map_sub, complexCopyToReal_X_zero,
        complexCopyToReal_X_one]
      simp only [smul_sub, smul_add, smul_smul]
      match_scalars
      all_goals ring_nf
      all_goals norm_num [Complex.I_sq]
  exact congrArg (fun T => T p) h

theorem realCopyToComplex_complexCopyToReal (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    realCopyToComplex m (complexCopyToReal m p) = p := by
  have h : (realCopyToComplex m).comp (complexCopyToReal m) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a,j⟩
    fin_cases a
    · change realCopyToComplex m (complexCopyToReal m (X (0,j))) = X (0,j)
      rw [complexCopyToReal_X_zero, map_add, map_smul, realCopyToComplex_X_zero,
        realCopyToComplex_X_one]
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]
    · change realCopyToComplex m (complexCopyToReal m (X (1,j))) = X (1,j)
      rw [complexCopyToReal_X_one, map_sub, map_smul, realCopyToComplex_X_zero,
        realCopyToComplex_X_one]
      match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]
  exact congrArg (fun T => T p) h

private def copyBalanceDeriv (m : ℕ) :
    Derivation ℂ (MvPolynomial (Fin 2 × Fin m) ℂ)
      (MvPolynomial (Fin 2 × Fin m) ℂ) :=
  mkDerivation ℂ (fun ai => if ai.1 = 0 then X ai else -X ai)

private theorem copyBalanceDeriv_eq (m : ℕ) (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    copyBalanceDeriv m p = copyModeEuler m 0 p - copyModeEuler m 1 p := by
  classical
  have h : copyBalanceDeriv m = ∑ j : Fin m,
      ((X (0,j) : MvPolynomial (Fin 2 × Fin m) ℂ) • pderiv (0,j) -
        (X (1,j) : MvPolynomial (Fin 2 × Fin m) ℂ) • pderiv (1,j)) := by
    apply derivation_ext
    rintro ⟨a,j⟩
    fin_cases a <;>
      simp [copyBalanceDeriv, mkDerivation_X, pderiv_X, Pi.single_apply,
        Prod.ext_iff, eq_comm]
  rw [h]
  simp [copyModeEuler, Finset.sum_sub_distrib]

private def lambdaPolynomialDeriv (m : ℕ) :
    Derivation ℂ (MvPolynomial (Fin 2 × Fin m) ℂ)
      (MvPolynomial (Fin 2 × Fin m) ℂ) :=
  Complex.I • polynomialRotationDeriv m

private theorem lambdaPolynomialDeriv_eq (m : ℕ) (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    lambdaPolynomialDeriv m p = polynomialLambda m p := by
  change Complex.I • polynomialRotationDeriv m p = _
  rw [polynomialRotationDeriv_eq, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

private theorem complexCopyToReal_balance (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialLambda m (complexCopyToReal m p) = complexCopyToReal m (copyBalanceDeriv m p) := by
  have hX (ai : Fin 2 × Fin m) :
      lambdaPolynomialDeriv m (complexCopyToReal m (X ai)) =
        complexCopyToReal m (copyBalanceDeriv m (X ai)) := by
    rcases ai with ⟨a,j⟩
    fin_cases a <;>
      simp [lambdaPolynomialDeriv, complexCopyToReal, copyBalanceDeriv,
        polynomialRotationDeriv, mkDerivation_X, smul_add, smul_smul]
    all_goals module
  rw [← lambdaPolynomialDeriv_eq]
  induction p using MvPolynomial.induction_on with
  | C c => simp [complexCopyToReal]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ai hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX]

/-- Vanishing of the physical polynomial generator is equality of the two
Euler degrees in complex copy coordinates. -/
theorem realCopyToComplex_balanced {m : ℕ}
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) (hp : polynomialLambda m p = 0) :
    copyModeEuler m 0 (realCopyToComplex m p) =
      copyModeEuler m 1 (realCopyToComplex m p) := by
  have h := complexCopyToReal_balance m (realCopyToComplex m p)
  rw [complexCopyToReal_realCopyToComplex, hp] at h
  have hzero : copyBalanceDeriv m (realCopyToComplex m p) = 0 := by
    have hc := congrArg (realCopyToComplex m) h
    simpa only [map_zero, realCopyToComplex_complexCopyToReal] using hc.symm
  exact sub_eq_zero.mp ((copyBalanceDeriv_eq m _).symm.trans hzero)

/-- Reflection of the second real copy coordinate. -/
def copyPolynomialReflection (m : ℕ) :
    MvPolynomial (Fin 2 × Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin 2 × Fin m) ℂ :=
  aeval (fun ai => if ai.1 = 0 then X ai else -X ai)

theorem copyPolynomialReflection_eq_swap_rotate (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    copyPolynomialReflection m p = copyModeSwap m (polynomialRotate m (Real.pi / 2) p) := by
  have h : copyPolynomialReflection m =
      (copyModeSwap m).comp (polynomialRotate m (Real.pi / 2)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a,j⟩
    fin_cases a <;> simp [copyPolynomialReflection, polynomialRotate, copyModeSwap]
  exact congrArg (fun T => T p) h

theorem realCopyToComplex_reflection (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    realCopyToComplex m (copyPolynomialReflection m p) =
      copyModeSwap m (realCopyToComplex m p) := by
  have h : (realCopyToComplex m).comp (copyPolynomialReflection m) =
      (copyModeSwap m).comp (realCopyToComplex m) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a,j⟩
    fin_cases a <;>
      simp [copyPolynomialReflection, realCopyToComplex, copyModeSwap]
    all_goals module
  exact congrArg (fun T => T p) h

/-- A physical quarter-turn invariant, swap invariant polynomial becomes
swap invariant in complex copy coordinates. -/
theorem realCopyToComplex_swap {m : ℕ}
    (p : MvPolynomial (Fin 2 × Fin m) ℂ)
    (hquarter : polynomialRotate m (Real.pi / 2) p = p) (hswap : copyModeSwap m p = p) :
    copyModeSwap m (realCopyToComplex m p) = realCopyToComplex m p := by
  rw [← realCopyToComplex_reflection, copyPolynomialReflection_eq_swap_rotate, hquarter, hswap]

/-- The complex symmetric mixed quadratic is twice the real Gram entry. -/
theorem complexCopyToReal_symmetricMixedPolynomial (m : ℕ) (i j : Fin m) :
    complexCopyToReal m (symmetricMixedPolynomial m i j) = (2 : ℂ) • copyGramPolynomial m i j := by
  simp only [symmetricMixedPolynomial, map_add, map_mul, complexCopyToReal_X_zero,
    complexCopyToReal_X_one, copyGramPolynomial]
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  simp only [mul_comm]
  match_scalars
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem complexCopyToReal_mem_copyGramAlgebra {m : ℕ}
    {p : MvPolynomial (Fin 2 × Fin m) ℂ} (hp : p ∈ symmetricMixedAlgebra m) :
    complexCopyToReal m p ∈ copyGramAlgebra m := by
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨⟨i,j⟩, rfl⟩ := hp
    rw [complexCopyToReal_symmetricMixedPolynomial]
    exact (copyGramAlgebra m).smul_mem (copyGramPolynomial_mem m i j) 2
  | algebraMap c => simpa only [AlgHom.commutes] using (copyGramAlgebra m).algebraMap_mem c
  | add p q _ _ hp hq => simpa only [map_add] using (copyGramAlgebra m).add_mem hp hq
  | mul p q _ _ hp hq => simpa only [map_mul] using (copyGramAlgebra m).mul_mem hp hq

end
end GaussianTesting
