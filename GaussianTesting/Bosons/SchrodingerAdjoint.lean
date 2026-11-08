module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerDerivative
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Creation and annihilation are adjoint on polynomial Gaussians

Gaussian integration by parts gives the actual `L²` adjoint relation on the
finite polynomial core. The one-dimensional moment identity is lifted by
Fubini to arbitrary finite collections of modes.
-/

namespace GaussianTesting

open MeasureTheory MvPolynomial
open scoped InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false

private def gaussianMoment (n : ℕ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) ^ n * (Real.exp (-x ^ 2) : ℂ)

private theorem integrable_gaussianMoment (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * (Real.exp (-x ^ 2) : ℂ)) := by
  have h : Integrable (fun x : ℝ => ((x ^ (n : ℝ) * Real.exp (-1 * x ^ 2) : ℝ) : ℂ)) :=
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    (show (-1 : ℝ) < (n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).ofReal
  simpa only [Real.rpow_natCast, neg_one_mul, Complex.ofReal_mul, Complex.ofReal_pow] using h

private theorem gaussianMoment_recurrence (n : ℕ) :
    (n : ℂ) * gaussianMoment (n-1) = 2 * gaussianMoment (n+1) := by
  let u : ℝ → ℂ := fun x => (x : ℂ) ^ n
  let u' : ℝ → ℂ := fun x => (n : ℂ) * (x : ℂ) ^ (n-1)
  let v : ℝ → ℂ := fun x => Real.exp (-x ^ 2)
  let v' : ℝ → ℂ := fun x => -2 * (x : ℂ) * (Real.exp (-x ^ 2) : ℂ)
  have hu (x) : HasDerivAt u (u' x) x := by
    convert ((hasDerivAt_id x).pow n).ofReal_comp using 1 <;> simp [u, u']
  have hv (x) : HasDerivAt v (v' x) x := by
    convert (((hasDerivAt_id x).pow 2).neg.exp).ofReal_comp using 1
    · rfl
    · simp [v']
      ring_nf
  have huv' : Integrable (u * v') := by
    convert (integrable_gaussianMoment (n+1)).const_mul (-2 : ℂ) using 1
    funext x
    simp only [Pi.mul_apply, u, v', pow_succ]
    ring_nf
  have hu'v : Integrable (u' * v) := by
    convert (integrable_gaussianMoment (n-1)).const_mul (n : ℂ) using 1
    funext x
    simp only [Pi.mul_apply, u', v]
    ring_nf
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hu x) (fun x _ => hv x) huv' hu'v (integrable_gaussianMoment n)
  have hleft : (∫ x, u x * v' x) = -2 * gaussianMoment (n+1) := by
    unfold gaussianMoment
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp [u, v']; rw [pow_succ]; ring_nf
  have hright : (∫ x, u' x * v x) = (n : ℂ) * gaussianMoment (n-1) := by
    unfold gaussianMoment
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp [u', v]; ring_nf
  rw [hleft, hright] at h
  linear_combination h

variable {ι : Type*} [Fintype ι]

private def gaussianPolynomialIntegral : MvPolynomial ι ℂ →ₗ[ℂ] ℂ :=
  (innerSL ℂ (polynomialGaussian (1 : MvPolynomial ι ℂ))).toLinearMap.comp
    polynomialGaussianLinear

private theorem gaussianPolynomialIntegral_eq_integral (P : MvPolynomial ι ℂ) :
    gaussianPolynomialIntegral P = ∫ x : EuclideanSpace ℝ ι,
      eval (fun j => (x j : ℂ)) P * (Real.exp (-‖x‖ ^ 2) : ℂ) := by
  change inner ℂ (polynomialGaussian (1 : MvPolynomial ι ℂ)) (polynomialGaussian P) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [polynomialGaussian_coeFn (1 : MvPolynomial ι ℂ),
    polynomialGaussian_coeFn P] with x h1 hP
  rw [h1, hP]
  simp only [polynomialGaussianFun, map_one, one_mul, RCLike.inner_apply,
    Complex.conj_ofReal]
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring_nf

private theorem gaussianPolynomialIntegral_monomial (d : ι →₀ ℕ) (c : ℂ) :
    gaussianPolynomialIntegral (monomial d c) = c * ∏ j, gaussianMoment (d j) := by
  classical
  rw [gaussianPolynomialIntegral_eq_integral]
  simp only [eval_monomial]
  have hprod (x : EuclideanSpace ℝ ι) :
      d.prod (fun j n => (x j : ℂ) ^ n) = ∏ j, (x j : ℂ) ^ (d j) :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  simp_rw [hprod]
  have hg (x : EuclideanSpace ℝ ι) :
      (Real.exp (-‖x‖ ^ 2) : ℂ) = ∏ j, (Real.exp (-(x j) ^ 2) : ℂ) := by
    rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_neg_distrib, Real.exp_sum,
      Complex.ofReal_prod]
  simp_rw [hg, mul_assoc, ← Finset.prod_mul_distrib]
  rw [integral_const_mul]
  congr 1
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  exact integral_fintype_prod_volume_eq_prod
    (fun j (x : ℝ) => (x : ℂ) ^ (d j) * (Real.exp (-x ^ 2) : ℂ))

private theorem gaussianPolynomialIntegral_pderiv (P : MvPolynomial ι ℂ) (j : ι) :
    gaussianPolynomialIntegral (pderiv j P) =
      2 * gaussianPolynomialIntegral (X j * P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add, mul_add] using congrArg₂ (· + ·) hP hQ
  | monomial d c =>
    rw [pderiv_monomial, gaussianPolynomialIntegral_monomial, X, monomial_mul_monomial,
      one_mul, gaussianPolynomialIntegral_monomial]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hm (k : ι) (hk : k ∈ Finset.univ.erase j) :
        (d - (Finsupp.single j 1 : ι →₀ ℕ)) k = d k := by
      simp [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hk)]
    have hp (k : ι) (hk : k ∈ Finset.univ.erase j) :
        ((Finsupp.single j 1 : ι →₀ ℕ) + d) k = d k := by
      simp [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hk)]
    rw [Finset.prod_congr rfl (fun k hk => congrArg gaussianMoment (hm k hk)),
      Finset.prod_congr rfl (fun k hk => congrArg gaussianMoment (hp k hk))]
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
    have h := gaussianMoment_recurrence (d j)
    rw [add_comm 1 (d j)]
    linear_combination c * (∏ k ∈ Finset.univ.erase j, gaussianMoment (d k)) * h

omit [Fintype ι] in
private theorem eval_conjugatePolynomial (P : MvPolynomial ι ℂ)
    (x : EuclideanSpace ℝ ι) :
    eval (fun j => (x j : ℂ)) (MvPolynomial.map (starRingEnd ℂ) P) =
      star (eval (fun j => (x j : ℂ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP => simp [hP]

private theorem inner_polynomialGaussian_eq (P Q : MvPolynomial ι ℂ) :
    inner ℂ (polynomialGaussian P) (polynomialGaussian Q) =
      gaussianPolynomialIntegral (MvPolynomial.map (starRingEnd ℂ) P * Q) := by
  rw [L2.inner_def, gaussianPolynomialIntegral_eq_integral]
  apply integral_congr_ae
  filter_upwards [polynomialGaussian_coeFn P, polynomialGaussian_coeFn Q] with x hP hQ
  rw [hP, hQ]
  simp only [polynomialGaussianFun, RCLike.inner_apply, map_mul,
    eval_conjugatePolynomial, starRingEnd_apply]
  rw [show star (Real.exp (-‖x‖ ^ 2 / 2) : ℂ) =
    (Real.exp (-‖x‖ ^ 2 / 2) : ℂ) from Complex.conj_ofReal _]
  have hg : (Real.exp (-‖x‖ ^ 2 / 2) : ℂ) * (Real.exp (-‖x‖ ^ 2 / 2) : ℂ) =
      (Real.exp (-‖x‖ ^ 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring_nf
  calc
    _ = (star (eval (fun j => (x j : ℂ)) P) * eval (fun j => (x j : ℂ)) Q) *
        ((Real.exp (-‖x‖ ^ 2 / 2) : ℂ) * (Real.exp (-‖x‖ ^ 2 / 2) : ℂ)) := by ring_nf
    _ = _ := by rw [hg]

omit [Fintype ι] in
private theorem conjugatePolynomial_creation (P : MvPolynomial ι ℂ) (j : ι) :
    MvPolynomial.map (starRingEnd ℂ) (polynomialCreation j P) =
      polynomialCreation j (MvPolynomial.map (starRingEnd ℂ) P) := by
  simp only [polynomialCreation_apply, MvPolynomial.smul_eq_C_mul, map_mul,
    map_sub, map_C, map_X, pderiv_map, map_inv₀, Complex.conj_ofReal, map_ofNat]

/-- Creation and annihilation on polynomial factors are actual Hilbert-space
adjoints on the finite polynomial Gaussian core. -/
theorem inner_polynomialGaussian_creation (P Q : MvPolynomial ι ℂ) (j : ι) :
    inner ℂ (polynomialGaussian (polynomialCreation j P)) (polynomialGaussian Q) =
      inner ℂ (polynomialGaussian P) (polynomialGaussian (polynomialAnnihilation j Q)) := by
  rw [inner_polynomialGaussian_eq, inner_polynomialGaussian_eq, conjugatePolynomial_creation]
  let S := MvPolynomial.map (starRingEnd ℂ) P
  have h := gaussianPolynomialIntegral_pderiv (S * Q) j
  rw [pderiv_mul, map_add] at h
  simp only [polynomialCreation_apply, polynomialAnnihilation_apply,
    smul_mul_assoc, mul_smul_comm, sub_mul, map_smul, map_sub, smul_eq_mul]
  change (Real.sqrt 2 : ℂ)⁻¹ *
      (2 * gaussianPolynomialIntegral (X j * S * Q) -
        gaussianPolynomialIntegral (pderiv j S * Q)) =
    (Real.sqrt 2 : ℂ)⁻¹ * gaussianPolynomialIntegral (S * pderiv j Q)
  rw [mul_assoc (X j) S Q]
  linear_combination -(Real.sqrt 2 : ℂ)⁻¹ * h

/-- The same finite-core adjoint identity with annihilation on the left. -/
theorem inner_polynomialGaussian_annihilation (P Q : MvPolynomial ι ℂ) (j : ι) :
    inner ℂ (polynomialGaussian (polynomialAnnihilation j P)) (polynomialGaussian Q) =
      inner ℂ (polynomialGaussian P) (polynomialGaussian (polynomialCreation j Q)) := by
  simpa only [← starRingEnd_apply, inner_conj_symm] using
    congrArg star (inner_polynomialGaussian_creation Q P j).symm

end
end GaussianTesting
