module

/-
Covariance moments and occupation observables used in manuscript Lemma 5.1.
The normal-form proof of the certainty characterization is in GaussianCertainty.lean.
The norm identity, saturation-to-eigenvector argument, and joint occupation
basis conclusion are steps of Lemma 5.1, not hypotheses of the preliminaries.
-/
public import GaussianTesting.Fermions.Gaussian

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {m : ℕ}

/-- Second moments `⟪ψ, c_a c_b ψ⟫`. -/
def majMoment (ψ : HF m) (a b : Fin m × Bool) : ℂ := ⟪ψ, maj a (maj b ψ)⟫_ℂ

/-- The covariance matrix `Γ_{ab} = (i/2)⟨[c_a, c_b]⟩_ψ` (real-valued). -/
def covMat (ψ : HF m) (a b : Fin m × Bool) : ℝ :=
  (Complex.I / 2 * (majMoment ψ a b - majMoment ψ b a)).re

lemma covMat_antisymm (ψ : HF m) (a b : Fin m × Bool) :
    covMat ψ b a = -covMat ψ a b := by
  unfold covMat
  simp only [mul_sub, Complex.sub_re]
  ring

@[simp] lemma covMat_diag (ψ : HF m) (a : Fin m × Bool) : covMat ψ a a = 0 := by
  simp [covMat]

/-- For unit `ψ`: `⟪ψ, c_a c_b ψ⟫ = δ_{ab} − i Γ_{ab}`. -/
lemma majMoment_eq {ψ : HF m} (hψ : ‖ψ‖ = 1) (a b : Fin m × Bool) :
    majMoment ψ a b
      = (if a = b then (1 : ℂ) else 0) - Complex.I * covMat ψ a b := by
  classical
  have hc : starRingEnd ℂ (majMoment ψ a b) = majMoment ψ b a := by
    unfold majMoment
    rw [inner_conj_symm, maj_isSymmetric a, maj_isSymmetric b]
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hψ]
  have hs : majMoment ψ a b + majMoment ψ b a =
      if a = b then (2 : ℂ) else 0 := by
    unfold majMoment
    rw [← inner_add_right]
    by_cases hab : a = b
    · subst b
      have hh : maj a (maj a ψ) = ψ :=
        congrArg (fun T : HF m →ₗ[ℂ] HF m => T ψ) (maj_sq a)
      rw [hh, inner_add_right, hn]
      norm_num
    · have hh : maj a (maj b ψ) + maj b (maj a ψ) = 0 :=
        congrArg (fun T : HF m →ₗ[ℂ] HF m => T ψ) (maj_anticomm hab)
      simp [hh, hab]
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hc
  have hcr := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.conj_re, Complex.conj_im] at hr hi hcr
  apply Complex.ext <;> by_cases hab : a = b <;>
    simp [covMat, hab, Complex.mul_re, Complex.mul_im] at hr hi hcr ⊢ <;> linarith

/-- eq:norm-Gamma: `⟪Λψ⊗ψ, Λψ⊗ψ⟫ = 2m − ‖Γ‖₂²` for unit `ψ`. -/
theorem norm_lambdaF_tp2 {ψ : HF m} (hψ : ‖ψ‖ = 1) :
    ⟪lambdaF m (tp2 ψ ψ), lambdaF m (tp2 ψ ψ)⟫_ℂ
      = ((2 * m : ℝ) - ∑ a, ∑ b, covMat ψ a b ^ 2 : ℝ) := by
  classical
  have ht (u v : HF m) : lambdaF m (tp2 u v) =
      ∑ a, tp2 (maj a u) (maj a v) := by
    simp [lambdaF, LinearMap.sum_apply, opL_tp2, opR_tp2]
  rw [lambdaF_isSymmetric, ht, map_sum]
  simp only [ht, inner_sum, inner_tp2_tp2, ← pow_two]
  change (∑ a, ∑ b, majMoment ψ b a ^ 2) = _
  rw [Finset.sum_comm]
  have he (a b : Fin m × Bool) :
      majMoment ψ a b ^ 2 = (if a = b then (1 : ℂ) else 0) -
          ((covMat ψ a b ^ 2 : ℝ) : ℂ) := by
    rw [majMoment_eq hψ]
    by_cases hab : a = b
    · subst b; simp
    · simp [hab, pow_two, Complex.I_mul_I, mul_mul_mul_comm]
  simp_rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  push_cast
  simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]


/-! ### The occupation-sign operators -/

/-- `nOp k = i c_{k,ff} c_{k,tt}`, the Hermitian involution `(-1)^{1 + n_k}`
(diagonal `x ↦ if x k then 1 else -1`). -/
def nOp (k : Fin m) : HF m →ₗ[ℂ] HF m :=
  Complex.I • (maj (k, false) ∘ₗ maj (k, true))

@[simp] lemma nOp_apply (k : Fin m) (f : HF m) (x : Qm m) :
    nOp k f x = (if x k then 1 else -1) * f x := by
  have hs : jwSign (flipBit k x) k = jwSign x k := by
    unfold jwSign
    apply Finset.prod_congr rfl
    intro l hl
    have hne : l ≠ k := ne_of_lt (Finset.mem_filter.mp hl).2
    simp [flipBit, Function.update_of_ne hne]
  have hsq : jwSign x k * jwSign x k = 1 := by
    unfold jwSign
    rw [← Finset.prod_mul_distrib]
    have hsign (l : Fin m) :
        (if x l then (-1 : ℂ) else 1) * (if x l then (-1 : ℂ) else 1) = 1 := by
      cases x l <;> norm_num
    simp only [hsign, Finset.prod_const_one]
  change Complex.I * (maj (k, false) (maj (k, true) f) x) = _
  simp only [maj_apply, hs, flipBit_flipBit]
  simp only [flipBit, Function.update_self, majFactor]
  cases hx : x k <;> simp
  · calc
      _ = -(jwSign x k * jwSign x k) * f x := by
        linear_combination (jwSign x k * jwSign x k * f x) * Complex.I_mul_I
      _ = _ := by rw [hsq]; simp
  · calc
      _ = (jwSign x k * jwSign x k) * f x := by
        linear_combination -(jwSign x k * jwSign x k * f x) * Complex.I_mul_I
      _ = _ := by rw [hsq]; simp


/-- The key covariance entry is the `nOp` expectation:
`Γ_{(k,ff),(k,tt)} = Re ⟪ψ, nOp k ψ⟫`. -/
lemma covMat_pair (ψ : HF m) (k : Fin m) :
    covMat ψ (k, false) (k, true) = (⟪ψ, nOp k ψ⟫_ℂ).re := by
  have hab : (k, false) ≠ (k, true) := by simp
  have hh : maj (k, false) (maj (k, true) ψ) +
      maj (k, true) (maj (k, false) ψ) = 0 :=
    congrArg (fun T : HF m →ₗ[ℂ] HF m => T ψ) (maj_anticomm hab)
  have hm : majMoment ψ (k, false) (k, true) +
      majMoment ψ (k, true) (k, false) = 0 := by
    rw [majMoment, majMoment, ← inner_add_right, hh, inner_zero_right]
  unfold covMat nOp
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, inner_smul_right]
  change (Complex.I / 2 * (majMoment ψ (k, false) (k, true) -
    majMoment ψ (k, true) (k, false))).re =
      (Complex.I * majMoment ψ (k, false) (k, true)).re
  congr 1
  rw [eq_neg_of_add_eq_zero_right hm]
  ring


/-- Equality in Cauchy–Schwarz: a unit expectation of the Hermitian involution
`nOp k` forces an eigenvector. -/
lemma nOp_eigen_of_expectation {ψ : HF m} (hψ : ‖ψ‖ = 1) {k : Fin m} {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (h : (⟪ψ, nOp k ψ⟫_ℂ).re = ε) :
    nOp k ψ = (ε : ℂ) • ψ := by
  have hs : (nOp k).IsSymmetric := by
    intro u v
    simp only [PiLp.inner_apply, RCLike.inner_apply, nOp_apply, map_mul]
    apply Finset.sum_congr rfl
    intro x _
    cases x k <;> simp
  have hsq : nOp k (nOp k ψ) = ψ := by
    ext x
    simp only [nOp_apply]
    cases x k <;> simp
  have hn : ‖nOp k ψ‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hs, hsq]
    simp [inner_self_eq_norm_sq_to_K, hψ]
  have hz : ‖nOp k ψ - (ε : ℂ) • ψ‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hn, inner_smul_right]
    have hr : (⟪nOp k ψ, ψ⟫_ℂ).re = ε := by
      rw [hs]
      exact h
    rcases hε with rfl | rfl <;>
      norm_num [norm_smul, hψ, Complex.mul_re, hr]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))


/-- A joint `nOp`-eigenvector is a phase times an occupation basis state. -/
lemma joint_eigen_basis {ψ : HF m} (hψ : ‖ψ‖ = 1)
    (h : ∀ k : Fin m, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ nOp k ψ = (ε : ℂ) • ψ) :
    ∃ (x : Qm m) (c : ℂ), ‖c‖ = 1 ∧ ψ = c • EuclideanSpace.single x (1 : ℂ) := by
  classical
  choose ε hε he using h
  let x₀ : Qm m := fun k => decide (ε k = 1)
  have heval (k : Fin m) (x : Qm m) :
      (if x k then (1 : ℂ) else -1) * ψ x = (ε k : ℂ) * ψ x := by
    have hh := congrArg (fun f : HF m => f x) (he k)
    simpa only [nOp_apply, PiLp.smul_apply, smul_eq_mul] using hh
  have hsupport (x : Qm m) (hx : x ≠ x₀) : ψ x = 0 := by
    have hk : ∃ k, x k ≠ x₀ k := by
      by_contra hh
      exact hx (funext (by simpa using hh))
    obtain ⟨k, hk⟩ := hk
    have hv := heval k x
    rcases hε k with hh | hh
    · have hxk : x k = false := by
        simpa [x₀, hh] using hk
      simp [hxk, hh] at hv
      linear_combination -hv / 2
    · have hxk : x k = true := by
        have hn : ε k ≠ 1 := by rw [hh]; norm_num
        simpa [x₀, hn] using hk
      simp [hxk, hh] at hv
      linear_combination hv / 2
  have heq : ψ = ψ x₀ • EuclideanSpace.single x₀ (1 : ℂ) := by
    ext x
    by_cases hx : x = x₀
    · subst x; simp [EuclideanSpace.single]
    · simp [EuclideanSpace.single, hx, hsupport x hx]
  refine ⟨x₀, ψ x₀, ?_, heq⟩
  rw [heq, norm_smul] at hψ
  simpa [EuclideanSpace.single, PiLp.norm_single] using hψ


end

end GaussianTesting
