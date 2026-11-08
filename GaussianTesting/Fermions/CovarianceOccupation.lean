module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CovarianceAction
public import GaussianTesting.Fermions.SkewNormalFormOrientation

@[expose] public section

/-!
# Occupation saturation in Lemma 5.1

Once the covariance is in two-dimensional block form, its block coefficients
are expectations of the occupation-sign operators. Their absolute values are
at most one; equality in the total squared norm forces a joint occupation
eigenvector. These are steps of the manuscript's proof of Lemma 5.1.
-/

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset Matrix

noncomputable section

variable {m : ℕ}

/-- Each canonical two-dimensional block contributes twice its squared
coefficient to the covariance norm. -/
theorem sum_sq_skewBlockMatrix (c : Fin m → ℝ) :
    (∑ a, ∑ b, skewBlockMatrix c a b ^ 2) = 2 * ∑ k, c k ^ 2 := by
  classical
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, skewBlockMatrix]
  simp [Finset.sum_add_distrib, eq_comm]
  ring

/-- For a canonical covariance, maximal squared Hilbert--Schmidt norm means
that the squared occupation expectations sum to the number of modes. -/
theorem covMat_pair_sum_eq_of_skewBlockMatrix {ψ : HF m} {c : Fin m → ℝ}
    (hc : Matrix.of (covMat ψ) = skewBlockMatrix c)
    (hsum : (∑ a, ∑ b, covMat ψ a b ^ 2) = (2 * m : ℝ)) :
    (∑ k : Fin m, covMat ψ (k, false) (k, true) ^ 2) = m := by
  have hentry (a b : Fin m × Bool) : covMat ψ a b = skewBlockMatrix c a b :=
    congrFun (congrFun hc a) b
  have hnorm := sum_sq_skewBlockMatrix c
  simp_rw [hentry] at hsum ⊢
  simp only [skewBlockMatrix, ↓reduceIte, Bool.false_eq_true]
  linarith

/-- The occupation-sign operator preserves the norm. -/
theorem norm_nOp (k : Fin m) (ψ : HF m) : ‖nOp k ψ‖ = ‖ψ‖ := by
  have hs : (nOp k).IsSymmetric := by
    intro u v
    simp only [PiLp.inner_apply, RCLike.inner_apply, nOp_apply, map_mul]
    apply Finset.sum_congr rfl
    intro x hx
    cases x k <;> simp
  have hsq : nOp k (nOp k ψ) = ψ := by
    ext x
    simp only [nOp_apply]
    cases x k <;> simp
  have hn : ‖nOp k ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hs, hsq,
      ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  nlinarith [norm_nonneg (nOp k ψ), norm_nonneg ψ]

/-- Each canonical covariance coefficient is bounded by one, from the
occupation-sign expectation and Cauchy--Schwarz. -/
theorem abs_covMat_pair_le_one {ψ : HF m} (hψ : ‖ψ‖ = 1) (k : Fin m) :
    |covMat ψ (k, false) (k, true)| ≤ 1 := by
  rw [covMat_pair]
  calc
    |(⟪ψ, nOp k ψ⟫_ℂ).re| ≤ ‖⟪ψ, nOp k ψ⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ψ‖ * ‖nOp k ψ‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [norm_nOp, hψ]; norm_num

/-- Saturation of the sum of the squared occupation expectations forces every
occupation expectation to be a sign. -/
theorem covMat_pair_signs_of_sum_eq {ψ : HF m} (hψ : ‖ψ‖ = 1)
    (hsum : (∑ k : Fin m, covMat ψ (k, false) (k, true) ^ 2) = m) :
    ∀ k : Fin m, covMat ψ (k, false) (k, true) = 1 ∨
      covMat ψ (k, false) (k, true) = -1 := by
  have hle (k : Fin m) (_ : k ∈ (univ : Finset (Fin m))) :
      covMat ψ (k, false) (k, true) ^ 2 ≤ (1 : ℝ) := by
    obtain ⟨hl, hu⟩ := abs_le.mp (abs_covMat_pair_le_one hψ k)
    nlinarith
  have htotal : (∑ k : Fin m, covMat ψ (k, false) (k, true) ^ 2) =
      ∑ _ : Fin m, (1 : ℝ) := by simpa using hsum
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp htotal
  intro k
  have hk := heq k (mem_univ k)
  exact sq_eq_one_iff.mp hk

/-- The final occupation step of Lemma 5.1: saturation gives an occupation
basis vector up to a phase. -/
theorem exists_phase_basis_of_covMat_pair_sum {ψ : HF m} (hψ : ‖ψ‖ = 1)
    (hsum : (∑ k : Fin m, covMat ψ (k, false) (k, true) ^ 2) = m) :
    ∃ (x : Qm m) (z : ℂ), ‖z‖ = 1 ∧ ψ = z • EuclideanSpace.single x (1 : ℂ) := by
  apply joint_eigen_basis hψ
  intro k
  refine ⟨covMat ψ (k, false) (k, true), covMat_pair_signs_of_sum_eq hψ hsum k, ?_⟩
  exact nOp_eigen_of_expectation hψ (covMat_pair_signs_of_sum_eq hψ hsum k)
    (covMat_pair ψ k).symm

/-- A unit state with canonical covariance of maximal squared norm is an
occupation basis state up to phase, as in the proof of Lemma 5.1. -/
theorem exists_phase_basis_of_covMat_skewBlockMatrix {ψ : HF m}
    (hψ : ‖ψ‖ = 1) {c : Fin m → ℝ}
    (hc : Matrix.of (covMat ψ) = skewBlockMatrix c)
    (hsum : (∑ a, ∑ b, covMat ψ a b ^ 2) = (2 * m : ℝ)) :
    ∃ (x : Qm m) (z : ℂ), ‖z‖ = 1 ∧ ψ = z • EuclideanSpace.single x (1 : ℂ) := by
  exact exists_phase_basis_of_covMat_pair_sum hψ
    (covMat_pair_sum_eq_of_skewBlockMatrix hc hsum)

end

end GaussianTesting
