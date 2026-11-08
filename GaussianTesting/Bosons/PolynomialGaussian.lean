module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic

@[expose] public section

/-! # Polynomial Gaussian wavefunctions in Lebesgue `L²` -/

namespace GaussianTesting

open MeasureTheory MvPolynomial
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {ι : Type*} [Fintype ι]

/-- A polynomial times the oscillator vacuum Gaussian, without its normalization
constant. Multiplying by the vacuum normalization does not change the finite core. -/
def polynomialGaussianFun (p : MvPolynomial ι ℂ) (x : EuclideanSpace ℝ ι) : ℂ :=
  eval (fun i => (x i : ℂ)) p * (Real.exp (-‖x‖ ^ 2 / 2) : ℂ)

lemma polynomialGaussianFun_continuous (p : MvPolynomial ι ℂ) :
    Continuous (polynomialGaussianFun p) := by
  unfold polynomialGaussianFun
  apply Continuous.mul
  · exact p.continuous_eval.comp (continuous_pi fun i =>
      Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ i))
  · fun_prop

private lemma polynomialGaussianFun_monomial_norm_sq
    (d : ι →₀ ℕ) (x : EuclideanSpace ℝ ι) :
    ‖polynomialGaussianFun (monomial d (1 : ℂ)) x‖ ^ 2 =
      ∏ i, x i ^ (2 * d i) * Real.exp (-(x i) ^ 2) := by
  classical
  rw [polynomialGaussianFun, eval_monomial]
  simp only [one_mul]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [norm_mul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [← Finset.prod_pow]
  have he : (2 : ℝ) * (-‖x‖ ^ 2 / 2) = -∑ i, x i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    ring
  rw [he, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, Nat.mul_comm (d i) 2, pow_mul, sq_abs, ← pow_mul]

private lemma integrable_polynomialGaussianFun_monomial_norm_sq (d : ι →₀ ℕ) :
    Integrable (fun x : EuclideanSpace ℝ ι =>
      ‖polynomialGaussianFun (monomial d (1 : ℂ)) x‖ ^ 2) := by
  simp_rw [polynomialGaussianFun_monomial_norm_sq]
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  change Integrable (fun x : ι → ℝ => ∏ i, x i ^ (2 * d i) *
    Real.exp (-(x i) ^ 2)) (Measure.pi fun _ => (volume : Measure ℝ))
  apply Integrable.fintype_prod (f := fun i (x : ℝ) =>
    x ^ (2 * d i) * Real.exp (-x ^ 2))
  intro i
  have hs : (-1 : ℝ) < ((2 * d i : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)
  simpa only [Real.rpow_natCast, neg_mul, one_mul] using
    integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1) hs

/-- Every polynomial Gaussian is square-integrable with respect to Lebesgue measure. -/
theorem polynomialGaussianFun_memLp (p : MvPolynomial ι ℂ) :
    MemLp (polynomialGaussianFun p) 2 volume := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have h : MemLp (polynomialGaussianFun (monomial d (1 : ℂ))) 2 volume :=
      (memLp_two_iff_integrable_sq_norm
        (polynomialGaussianFun_continuous _).aestronglyMeasurable).mpr
          (integrable_polynomialGaussianFun_monomial_norm_sq d)
    convert h.const_smul c using 1
    funext x
    simp only [Pi.smul_apply, polynomialGaussianFun, eval_monomial, smul_eq_mul, one_mul]
    ring
  | add p q hp hq =>
    convert hp.add hq using 1
    funext x
    simp [polynomialGaussianFun, add_mul]

/-- The polynomial Gaussian as an element of actual Lebesgue `L²`. -/
def polynomialGaussian (p : MvPolynomial ι ℂ) :
    MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
  (polynomialGaussianFun_memLp p).toLp (polynomialGaussianFun p)

lemma polynomialGaussian_coeFn (p : MvPolynomial ι ℂ) :
    polynomialGaussian p =ᵐ[volume] polynomialGaussianFun p :=
  MemLp.coeFn_toLp _

lemma polynomialGaussian_add (p q : MvPolynomial ι ℂ) :
    polynomialGaussian (p + q) = polynomialGaussian p + polynomialGaussian q := by
  apply Lp.ext
  filter_upwards [polynomialGaussian_coeFn (p+q), polynomialGaussian_coeFn p,
    polynomialGaussian_coeFn q, Lp.coeFn_add (polynomialGaussian p) (polynomialGaussian q)]
    with x hpq hp hq ha
  rw [hpq, ha, Pi.add_apply, hp, hq]
  simp [polynomialGaussianFun, add_mul]

lemma polynomialGaussian_smul (c : ℂ) (p : MvPolynomial ι ℂ) :
    polynomialGaussian (c • p) = c • polynomialGaussian p := by
  apply Lp.ext
  filter_upwards [polynomialGaussian_coeFn (c • p), polynomialGaussian_coeFn p,
    Lp.coeFn_smul c (polynomialGaussian p)] with x hcp hp hs
  rw [hcp, hs, Pi.smul_apply, hp]
  simp [polynomialGaussianFun, mul_assoc]

/-- The finite-core realization is complex linear. -/
def polynomialGaussianLinear : MvPolynomial ι ℂ →ₗ[ℂ]
    MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) where
  toFun := polynomialGaussian
  map_add' := polynomialGaussian_add
  map_smul' := polynomialGaussian_smul

end

end GaussianTesting
