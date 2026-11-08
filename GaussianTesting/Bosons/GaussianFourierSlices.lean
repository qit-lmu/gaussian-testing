module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.WaveGaussian
public import GaussianTesting.Bosons.CharacteristicInjectivity
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-!
# Fourier slices of Gaussian characteristic functions

The positive momentum block makes each frequency slice integrable. Gaussian
integration also makes its inverse Fourier transform integrable, allowing
Fourier uniqueness to recover the position correlation without regularity
assumptions on the original `L²` wavefunction.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure FourierTransform
open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

private theorem inverse_basis_sum {m : ℕ}
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (x : WaveConfig m) :
    x = ∑ i, (A x i) • A.symm (EuclideanSpace.single i 1) := by
  classical
  have hx : A x = ∑ i, A x i • EuclideanSpace.single i 1 := by
    ext j
    simp [Pi.single_apply]
  have h := congrArg A.symm hx
  simpa only [A.symm_apply_apply, _root_.map_sum, map_smul] using h

/-- The real quadratic decay of the inverse Gaussian Fourier integral. -/
def waveGaussianDualQuadratic {m : ℕ} (b : Fin m → ℝ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) : QuadraticForm ℝ (WaveConfig m) :=
  ∑ i, (Real.pi^2 / b i) • QuadraticMap.linMulLin
    (innerSL ℝ (A.symm (EuclideanSpace.single i 1))).toLinearMap
    (innerSL ℝ (A.symm (EuclideanSpace.single i 1))).toLinearMap

theorem waveGaussianDualQuadratic_apply {m : ℕ} (b : Fin m → ℝ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (x : WaveConfig m) :
    waveGaussianDualQuadratic b A x =
      ∑ i, (Real.pi^2 / b i) * (inner ℝ x (A.symm (EuclideanSpace.single i 1)))^2 := by
  simp [waveGaussianDualQuadratic, QuadraticMap.linMulLin_apply, pow_two, real_inner_comm]

/-- The inverse-coordinate vectors span, so the dual Gaussian quadratic form
is positive definite whenever the original diagonal coefficients are positive. -/
theorem waveGaussianDualQuadratic_posDef {m : ℕ} (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    (waveGaussianDualQuadratic b A).PosDef := by
  classical
  intro x hx
  rw [waveGaussianDualQuadratic_apply]
  have hnonneg (i : Fin m) : 0 ≤ Real.pi^2 / b i *
      (inner ℝ x (A.symm (EuclideanSpace.single i 1)))^2 :=
    mul_nonneg (div_nonneg (sq_nonneg _) (hb i).le) (sq_nonneg _)
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hnonneg i))
  intro hz
  have hi (i : Fin m) : inner ℝ x (A.symm (EuclideanSpace.single i 1)) = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hz.symm i (Finset.mem_univ i)
    have hp : 0 < Real.pi^2 / b i := div_pos (sq_pos_of_pos Real.pi_pos) (hb i)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hp.ne')
  apply hx
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  conv_lhs => rhs; rw [inverse_basis_sum A x]
  simp only [inner_sum, inner_smul_right, hi, mul_zero, Finset.sum_const_zero]

/-- The complex linear term after the inverse Fourier transform. -/
def waveGaussianDualLinear {m : ℕ} (b : Fin m → ℝ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (L : WaveConfig m →ₗ[ℝ] ℂ) :
    WaveConfig m →ₗ[ℝ] ℂ :=
  ∑ i, ((Real.pi : ℂ) * Complex.I * L (A.symm (EuclideanSpace.single i 1)) / b i) •
    (Complex.ofRealCLM.toLinearMap.comp
      (innerSL ℝ (A.symm (EuclideanSpace.single i 1))).toLinearMap)

private theorem gaussian_inverse_exponent (b : ℝ) (hb : b ≠ 0) (c : ℂ) (u : ℝ) :
    (c + (2 * Real.pi : ℝ) * Complex.I * (u : ℂ))^2 / (4 * b) =
      c^2 / (4 * b) - (Real.pi^2 / b * u^2 : ℝ) +
        ((Real.pi : ℂ) * Complex.I * c / b) * u := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The inverse Gaussian Fourier transform is another Gaussian with
positive real quadratic decay; its constant may be complex. -/
theorem fourierInv_quadratic_waveGaussian_shape {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m))
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (hb : ∀ i, 0 < b i) (hA : ∀ x, Q x = ∑ i, b i * (A x i)^2)
    (L : WaveConfig m →ₗ[ℝ] ℂ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ x,
      𝓕⁻ (fun t => Complex.exp (-(Q t : ℂ) + L t)) x =
        C * Complex.exp (-(waveGaussianDualQuadratic b A x : ℂ) + waveGaussianDualLinear b A L x) := by
  classical
  let c (i : Fin m) := L (A.symm (EuclideanSpace.single i 1))
  let k (i : Fin m) : ℂ := (Real.pi / (b i : ℂ)) ^ (1/2 : ℂ)
  let d : ℝ := |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹|
  let C : ℂ := d * (∏ i, k i) * Complex.exp (∑ i, c i ^ 2 / (4 * b i))
  have hd : d ≠ 0 := abs_ne_zero.mpr (inv_ne_zero (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero)
  have hk (i : Fin m) : k i ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Complex.ofReal_ne_zero.mpr (hb i).ne')
  refine ⟨C, mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hd)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hk i))) (Complex.exp_ne_zero _), ?_⟩
  intro x
  rw [fourierInv_quadratic_waveGaussian Q b A hb hA L x]
  simp only [Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hsum : (∑ i, (c i + (2 * Real.pi : ℝ) * Complex.I *
      (inner ℝ x (A.symm (EuclideanSpace.single i 1)) : ℂ))^2 / (4 * b i)) =
      (∑ i, c i^2 / (4 * b i)) - (waveGaussianDualQuadratic b A x : ℂ) +
        waveGaussianDualLinear b A L x := by
    simp_rw [gaussian_inverse_exponent _ (hb _).ne']
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, waveGaussianDualQuadratic_apply]
    simp only [waveGaussianDualLinear, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply,
      innerSL_apply_apply, smul_eq_mul, real_inner_comm,
      Complex.ofReal_sum]
    rfl
  change (d : ℂ) * ((∏ i, k i) * Complex.exp _) = C * Complex.exp _
  rw [hsum]
  dsimp [C]
  rw [show (∑ i, c i^2 / (4 * b i)) - (waveGaussianDualQuadratic b A x : ℂ) +
      waveGaussianDualLinear b A L x =
      (∑ i, c i^2 / (4 * b i)) + (-(waveGaussianDualQuadratic b A x : ℂ) +
      waveGaussianDualLinear b A L x) by ring, Complex.exp_add]
  ring

/-- The inverse Fourier transform of a positive quadratic Gaussian with any
complex linear term is integrable. -/
theorem integrable_fourierInv_quadratic_waveGaussian {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m)) (hQ : Q.PosDef) (L : WaveConfig m →ₗ[ℝ] ℂ) :
    Integrable (𝓕⁻ (fun t => Complex.exp (-(Q t : ℂ) + L t))) := by
  obtain ⟨b, A, hb, hA⟩ := positiveQuadratic_diagonal_coordinates Q hQ
  obtain ⟨C, _, hC⟩ := fourierInv_quadratic_waveGaussian_shape Q b A hb hA L
  have h := (integrable_quadratic_waveGaussian (waveGaussianDualQuadratic b A)
    (waveGaussianDualQuadratic_posDef b hb A) (waveGaussianDualLinear b A L)).const_mul C
  simpa only [← hC] using h

end
end GaussianTesting
