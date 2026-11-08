module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PolynomialGaussian
public import GaussianTesting.Bosons.FourierUniqueness
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

/-!
# Density of polynomial Gaussian wavefunctions

Orthogonality to all polynomial Gaussians forces the Fourier transform of a
Gaussian-weighted wavefunction to vanish. The exponential series is dominated
by an integrable Gaussian times the input's norm, so no moment assumption on
an arbitrary `L²` input is needed.
-/

namespace GaussianTesting

open MeasureTheory MvPolynomial FourierTransform Filter
open scoped InnerProductSpace Topology

noncomputable section

variable {ι : Type*} [Fintype ι]

private theorem gaussian_quarter_memLp :
    MemLp (fun x : EuclideanSpace ℝ ι => Real.exp (-‖x‖ ^ 2 / 4)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ ι) (b := (1/2 : ℂ)) (by norm_num) 0 0).re
  convert h using 1
  funext x
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-‖x‖ ^ 2 / 4) = -‖x‖ ^ 2 / 2 by ring]
  have he : -(1/2 : ℂ) * (‖x‖ : ℂ) ^ 2 + 0 * (inner ℝ (0 : EuclideanSpace ℝ ι) x : ℂ) =
      ((-‖x‖ ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp]
  rfl

private theorem integrable_gaussian_dominator
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (C : ℝ) :
    Integrable (fun x => Real.exp (C ^ 2) *
      (‖f x‖ * Real.exp (-‖x‖ ^ 2 / 4))) := by
  exact ((Lp.memLp f).norm.integrable_mul gaussian_quarter_memLp).const_mul _

private theorem gaussian_exponential_bound (C a : ℝ) :
    Real.exp (C * a) * Real.exp (-a ^ 2 / 2) ≤
      Real.exp (C ^ 2) * Real.exp (-a ^ 2 / 4) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (C - a/2)]

private def frequencyPolynomial (t : EuclideanSpace ℝ ι) : MvPolynomial ι ℂ :=
  C (-2 * (Real.pi : ℂ) * Complex.I) * ∑ j, C (t j : ℂ) * X j

private theorem frequencyPolynomial_eval (t x : EuclideanSpace ℝ ι) :
    eval (fun j => (x j : ℂ)) (frequencyPolynomial t) =
      ((-2 * Real.pi * inner ℝ x t : ℝ) : ℂ) * Complex.I := by
  classical
  simp only [frequencyPolynomial, map_mul, map_sum, eval_C, eval_X,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem norm_exp_partial_sum_le (z : ℂ) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z ^ k / (k.factorial : ℂ)‖ ≤ Real.exp ‖z‖ := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖z ^ k / (k.factorial : ℂ)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range n, ‖z‖ ^ k / (k.factorial : ℝ) := by simp
    _ ≤ _ := Real.sum_le_exp_of_nonneg (norm_nonneg _) n

/-- Orthogonality to every polynomial Gaussian forces an arbitrary wavefunction
to vanish; no regularity or moment assumption is imposed on the input. -/
theorem eq_zero_of_inner_polynomialGaussian_eq_zero
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
    (horth : ∀ p : MvPolynomial ι ℂ, inner ℂ f (polynomialGaussian p) = 0) : f = 0 := by
  classical
  let w : EuclideanSpace ℝ ι → ℂ := fun x =>
    (Real.exp (-‖x‖ ^ 2 / 2) : ℂ) * star (f x)
  have hw : Integrable w := by
    apply (L2.integrable_inner f (polynomialGaussian (1 : MvPolynomial ι ℂ))).congr
    filter_upwards [polynomialGaussian_coeFn (1 : MvPolynomial ι ℂ)] with x hx
    simp only [hx, polynomialGaussianFun, map_one, one_mul, RCLike.inner_apply,
      starRingEnd_apply, w]
  have hF : ∀ t, 𝓕 w t = 0 := by
    intro t
    let z : EuclideanSpace ℝ ι → ℂ := fun x =>
      ((-2 * Real.pi * inner ℝ x t : ℝ) : ℂ) * Complex.I
    let C : ℝ := 2 * Real.pi * ‖t‖
    let F : ℕ → EuclideanSpace ℝ ι → ℂ := fun n x =>
      (∑ k ∈ Finset.range n, z x ^ k / (k.factorial : ℂ)) * w x
    let B : EuclideanSpace ℝ ι → ℝ := fun x =>
      Real.exp (C ^ 2) * (‖f x‖ * Real.exp (-‖x‖ ^ 2 / 4))
    have hz (x) : ‖z x‖ ≤ C * ‖x‖ := by
      dsimp [z, C]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        mul_one, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]
      calc
        _ ≤ (2 * Real.pi) * (‖x‖ * ‖t‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x t) (by positivity)
        _ = _ := by ring
    have hmeas (n : ℕ) : AEStronglyMeasurable (F n) volume := by
      dsimp [F, w, z]
      fun_prop
    have hbound (n : ℕ) : ∀ᵐ x ∂volume, ‖F n x‖ ≤ B x := by
      apply Filter.Eventually.of_forall
      intro x
      dsimp [F, w, B]
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_conj]
      calc
        _ ≤ Real.exp (C * ‖x‖) * (Real.exp (-‖x‖ ^ 2 / 2) * ‖f x‖) :=
          mul_le_mul_of_nonneg_right ((norm_exp_partial_sum_le (z x) n).trans
            (Real.exp_le_exp.mpr (hz x))) (by positivity)
        _ = (Real.exp (C * ‖x‖) * Real.exp (-‖x‖ ^ 2 / 2)) * ‖f x‖ := by ring
        _ ≤ (Real.exp (C ^ 2) * Real.exp (-‖x‖ ^ 2 / 4)) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right (gaussian_exponential_bound C ‖x‖) (norm_nonneg _)
        _ = _ := by ring
    have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop
        (𝓝 (Complex.exp (z x) * w x)) := by
      apply Filter.Eventually.of_forall
      intro x
      have he := (NormedSpace.expSeries_div_hasSum_exp (z x)).tendsto_sum_nat
      simpa only [F, ← Complex.exp_eq_exp_ℂ] using he.mul_const (w x)
    have hi := tendsto_integral_of_dominated_convergence B hmeas
      (integrable_gaussian_dominator f C) hbound hlim
    have hzero (n : ℕ) : ∫ x, F n x = 0 := by
      let P : MvPolynomial ι ℂ := ∑ k ∈ Finset.range n,
        ((k.factorial : ℂ)⁻¹) • (frequencyPolynomial t) ^ k
      have hP := horth P
      rw [L2.inner_def] at hP
      calc
        _ = ∫ x, inner ℂ (f x) (polynomialGaussian P x) := by
          apply integral_congr_ae
          filter_upwards [polynomialGaussian_coeFn P] with x hx
          rw [hx]
          have hEval : eval (fun j => (x j : ℂ)) P =
              ∑ k ∈ Finset.range n, z x ^ k / (k.factorial : ℂ) := by
            simp only [P, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
              map_pow, frequencyPolynomial_eval, z, div_eq_mul_inv]
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [polynomialGaussianFun, hEval]
          simp only [F, w, RCLike.inner_apply, starRingEnd_apply]
          ring
        _ = 0 := hP
    have hi' : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop
        (𝓝 (∫ x, Complex.exp (z x) * w x)) := by simpa only [hzero] using hi
    have := tendsto_nhds_unique tendsto_const_nhds hi'
    simpa only [Real.fourier_eq', smul_eq_mul, z] using this.symm
  have hwzero := ae_eq_zero_of_fourier_eq_zero hw hF
  apply Lp.ext
  filter_upwards [hwzero, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x hx hz
  rw [hz]
  have hx' : star (f x) = 0 :=
    (mul_eq_zero.mp hx).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  exact star_eq_zero.mp hx'

/-- Polynomial Gaussians span a dense subspace of the actual Schrödinger
Hilbert space for every finite set of modes. -/
theorem polynomialGaussian_range_topologicalClosure :
    (LinearMap.range (polynomialGaussianLinear (ι := ι))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  apply eq_zero_of_inner_polynomialGaussian_eq_zero f
  intro p
  exact (Submodule.mem_orthogonal' _ _).mp hf (polynomialGaussian p) ⟨p, rfl⟩

/-- The finite polynomial Gaussian realization has dense range in `L²`. -/
theorem denseRange_polynomialGaussian :
    DenseRange (polynomialGaussian (ι := ι)) := by
  change Dense (LinearMap.range (polynomialGaussianLinear (ι := ι)) :
    Set (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    polynomialGaussian_range_topologicalClosure

end
end GaussianTesting
