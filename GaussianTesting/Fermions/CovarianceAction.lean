module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CovarianceBasic
public import GaussianTesting.Fermions.GaussianImplementers

@[expose] public section

/-!
# Covariance under Gaussian implementers

The covariance reduction in the proof of Lemma 5.1 uses the transformation
`Γ(U†ψ) = Rᵀ Γ(ψ) R` and preservation of its squared Hilbert--Schmidt norm.
Here `U c_j U† = ∑ k, R_{kj} c_k`, as in `ImplementsMajoranaRotation`.
-/

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate Matrix
open Finset Matrix

noncomputable section

variable {m : ℕ}

private lemma covMat_eq_neg_im (ψ : HF m) (a b : Fin m × Bool) :
    covMat ψ a b = -(majMoment ψ a b).im := by
  have hc : starRingEnd ℂ (majMoment ψ a b) = majMoment ψ b a := by
    unfold majMoment
    rw [inner_conj_symm, maj_isSymmetric a, maj_isSymmetric b]
  rw [covMat, ← hc]
  simp [Complex.mul_re]
  ring

/-- The second moments transform by the same real congruence as the covariance. -/
theorem ImplementsMajoranaRotation.majMoment_symm {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (ψ : HF m) (a b : Fin m × Bool) :
    majMoment (U.symm ψ) a b =
      ∑ k, ∑ l, (R.val k a : ℂ) * (R.val l b : ℂ) * majMoment ψ k l := by
  classical
  unfold majMoment
  rw [← maj_isSymmetric a, ← U.inner_map_map, hU.majorana, hU.majorana]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro l hl
  rw [maj_isSymmetric k]
  ring

/-- Covariance congruence used in the canonical-form argument of Lemma 5.1. -/
theorem ImplementsMajoranaRotation.covMat_symm {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (ψ : HF m) :
    Matrix.of (covMat (U.symm ψ)) = R.valᵀ * Matrix.of (covMat ψ) * R.val := by
  classical
  ext a b
  simp only [Matrix.of_apply]
  rw [covMat_eq_neg_im, hU.majMoment_symm]
  simp only [Complex.im_sum, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero,
    ← Finset.sum_neg_distrib,
    Matrix.mul_apply, transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro l hl
  rw [covMat_eq_neg_im]
  ring

private lemma sum_sq_mulVec_of_transpose_mul {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : Aᵀ * A = 1) (v : ι → ℝ) :
    (∑ j, (A.mulVec v j) ^ 2) = ∑ j, v j ^ 2 := by
  have h := dotProduct_transpose_mulVec A v (A.mulVec v)
  rw [mulVec_mulVec, hA, one_mulVec] at h
  simpa only [dotProduct, pow_two] using h.symm

/-- Orthogonal congruence preserves the squared Hilbert--Schmidt norm. -/
theorem sum_sq_specialOrthogonal_congruence {ι : Type*} [Fintype ι]
    [DecidableEq ι] (R : Matrix.specialOrthogonalGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (∑ a, ∑ b, (R.valᵀ * A * R.val) a b ^ 2) = ∑ a, ∑ b, A a b ^ 2 := by
  have hRt : R.valᵀᵀ * R.valᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff ι ℝ).mp R.property.1
  have hright (B : Matrix ι ι ℝ) :
      (∑ a, ∑ b, (B * R.val) a b ^ 2) = ∑ a, ∑ b, B a b ^ 2 := by
    apply sum_congr rfl
    intro a ha
    simpa only [mulVec, dotProduct, mul_apply, transpose_apply, mul_comm] using
      sum_sq_mulVec_of_transpose_mul R.valᵀ hRt (B a)
  rw [hright, sum_comm]
  calc
    (∑ b, ∑ a, (R.valᵀ * A) a b ^ 2) = ∑ b, ∑ a, A a b ^ 2 := by
      apply sum_congr rfl
      intro b hb
      exact sum_sq_mulVec_of_transpose_mul R.valᵀ hRt (fun a => A a b)
    _ = _ := sum_comm

/-- The covariance norm is unchanged by a Gaussian implementer. -/
theorem ImplementsMajoranaRotation.sum_sq_covMat_symm {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (ψ : HF m) :
    (∑ a, ∑ b, covMat (U.symm ψ) a b ^ 2) = ∑ a, ∑ b, covMat ψ a b ^ 2 := by
  have h := congrArg
    (fun A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ => ∑ a, ∑ b, A a b ^ 2)
    (hU.covMat_symm ψ)
  exact h.trans (sum_sq_specialOrthogonal_congruence R (Matrix.of (covMat ψ)))

/-- Equivalently, the forward Gaussian action preserves the covariance norm. -/
theorem ImplementsMajoranaRotation.sum_sq_covMat {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (ψ : HF m) :
    (∑ a, ∑ b, covMat (U ψ) a b ^ 2) = ∑ a, ∑ b, covMat ψ a b ^ 2 := by
  simpa only [U.symm_apply_apply] using (hU.sum_sq_covMat_symm (U ψ)).symm

end

end GaussianTesting
