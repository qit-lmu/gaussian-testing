module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PolynomialGaussian
public import GaussianTesting.Bosons.SchrodingerDerivative
public import GaussianTesting.Bosons.SchrodingerTensor
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-!
# The normalized Schrödinger vacuum

The vacuum used in the coherent-state test is the normalized Gaussian
`π^(-m/4) exp(-‖x‖²/2)` in actual Lebesgue `L²(ℝ^m)`. Its normalization and
reflection invariance are proved directly, independently of the occupation
basis identification.
-/

namespace GaussianTesting

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The smooth Gaussian representative of the oscillator vacuum. -/
def waveVacuumFun (m : ℕ) (x : WaveConfig m) : ℂ :=
  ((Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ) * (Real.exp (-‖x‖ ^ 2 / 2) : ℂ)

/-- The normalized oscillator vacuum in the manuscript's position representation. -/
def waveVacuum (m : ℕ) : WaveSpace m :=
  ((Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ) •
    polynomialGaussian (1 : MvPolynomial (Fin m) ℂ)

/-- The vacuum has the standard Gaussian representative. -/
theorem waveVacuum_coeFn (m : ℕ) :
    (waveVacuum m : WaveConfig m → ℂ) =ᵐ[volume] waveVacuumFun m := by
  filter_upwards [Lp.coeFn_smul (((Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ))
      (polynomialGaussian (1 : MvPolynomial (Fin m) ℂ)),
    polynomialGaussian_coeFn (1 : MvPolynomial (Fin m) ℂ)] with x hx hy
  change (((Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ) •
    polynomialGaussian (1 : MvPolynomial (Fin m) ℂ)) x = _
  rw [hx]
  simp only [Pi.smul_apply, hy, polynomialGaussianFun, map_one, one_mul, smul_eq_mul,
    waveVacuumFun]

/-- Each actual coordinate annihilation operator `(Xⱼ + ∂ⱼ)/√2` annihilates
the Gaussian vacuum representative. -/
theorem waveVacuum_annihilation (m : ℕ) (x : WaveConfig m) (j : Fin m) :
    (Real.sqrt 2 : ℂ)⁻¹ * ((x j : ℂ) * waveVacuumFun m x +
      deriv (fun t : ℝ => waveVacuumFun m
        (x + t • EuclideanSpace.single j (1 : ℝ))) 0) = 0 := by
  let p : MvPolynomial (Fin m) ℂ :=
    MvPolynomial.C (((Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ))
  have hp (y : WaveConfig m) : polynomialGaussianFun p y = waveVacuumFun m y := by
    simp only [p, polynomialGaussianFun, MvPolynomial.eval_C, waveVacuumFun]
  have hz : polynomialAnnihilation j p = 0 := by
    simp [p, polynomialAnnihilation_apply]
  have h := polynomialGaussianFun_annihilation p x j
  rw [hz] at h
  simp only [hp] at h
  simpa only [polynomialGaussianFun, map_zero, zero_mul] using h.symm

private theorem gaussian_norm_sq (m : ℕ) :
    ‖polynomialGaussian (1 : MvPolynomial (Fin m) ℂ)‖ ^ 2 =
      Real.pi ^ ((m : ℝ) / 2) := by
  let f := polynomialGaussian (1 : MvPolynomial (Fin m) ℂ)
  change ‖f‖ ^ 2 = _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  calc
    (∫ x, RCLike.re (inner ℂ (f x) (f x))) =
        ∫ x : WaveConfig m, Real.exp (-‖x‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [polynomialGaussian_coeFn (1 : MvPolynomial (Fin m) ℂ)] with x hx
      change RCLike.re (inner ℂ (polynomialGaussian (1 : MvPolynomial (Fin m) ℂ) x)
        (polynomialGaussian (1 : MvPolynomial (Fin m) ℂ) x)) = _
      rw [hx]
      simp only [polynomialGaussianFun, map_one, one_mul,
        inner_self_eq_norm_sq_to_K, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), ← RCLike.ofReal_pow, RCLike.ofReal_re]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by
      simpa only [neg_one_mul, div_one, finrank_euclideanSpace_fin] using
        (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := WaveConfig m)
          (by norm_num : (0 : ℝ) < 1))

/-- The Gaussian vacuum is a unit vector for every number of modes. -/
theorem waveVacuum_norm (m : ℕ) : ‖waveVacuum m‖ = 1 := by
  have hsq : ‖waveVacuum m‖ ^ 2 = 1 := by
    rw [waveVacuum, norm_smul, mul_pow, gaussian_norm_sq]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos Real.pi_pos _)]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul Real.pi_pos.le,
      ← Real.rpow_add Real.pi_pos]
    rw [show -(m : ℝ) / 4 * (2 : ℕ) + (m : ℝ) / 2 = 0 by push_cast; ring,
      Real.rpow_zero]
  nlinarith [norm_nonneg (waveVacuum m)]

/-- Reflection leaves the vacuum fixed. -/
@[simp] theorem waveParity_vacuum (m : ℕ) : waveParity m (waveVacuum m) = waveVacuum m := by
  apply Lp.ext
  have hp : MeasurePreserving (fun x : WaveConfig m => -x) :=
    (LinearIsometryEquiv.neg ℝ : WaveConfig m ≃ₗᵢ[ℝ] WaveConfig m).measurePreserving
  filter_upwards [waveParity_coeFn m (waveVacuum m),
    hp.quasiMeasurePreserving.ae_eq_comp (waveVacuum_coeFn m),
    waveVacuum_coeFn m] with x hJ hneg hx
  simp only [Function.comp_apply] at hneg
  rw [hJ, hneg, hx]
  simp only [waveVacuumFun, norm_neg]

/-- The vacuum outcome projector `|0⟩⟨0|` on actual wavefunctions. -/
def waveVacuumProjection (m : ℕ) : WaveSpace m →L[ℂ] WaveSpace m :=
  InnerProductSpace.rankOne ℂ (waveVacuum m) (waveVacuum m)

@[simp] theorem waveVacuumProjection_apply (m : ℕ) (f : WaveSpace m) :
    waveVacuumProjection m f = inner ℂ (waveVacuum m) f • waveVacuum m := rfl

theorem waveVacuumProjection_symmetric (m : ℕ) (f g : WaveSpace m) :
    inner ℂ (waveVacuumProjection m f) g = inner ℂ f (waveVacuumProjection m g) :=
  InnerProductSpace.isSymmetric_rankOne_self (waveVacuum m) f g

@[simp] theorem waveVacuumProjection_idempotent (m : ℕ) (f : WaveSpace m) :
    waveVacuumProjection m (waveVacuumProjection m f) = waveVacuumProjection m f := by
  simp [waveVacuumProjection_apply, inner_self_eq_norm_sq_to_K,
    waveVacuum_norm]

/-- Reflection acts trivially on the vacuum outcome subspace. -/
@[simp] theorem waveParity_vacuumProjection (m : ℕ) (f : WaveSpace m) :
    waveParity m (waveVacuumProjection m f) = waveVacuumProjection m f := by
  simp only [waveVacuumProjection_apply, map_smul, waveParity_vacuum]

/-- Reflecting an input does not change its vacuum component. -/
@[simp] theorem waveVacuumProjection_parity (m : ℕ) (f : WaveSpace m) :
    waveVacuumProjection m (waveParity m f) = waveVacuumProjection m f := by
  have h : inner ℂ (waveVacuum m) (waveParity m f) = inner ℂ (waveVacuum m) f := by
    rw [← (waveParity m).inner_map_map (waveVacuum m) (waveParity m f),
      waveParity_vacuum, waveParity_involution]
  simp only [waveVacuumProjection_apply, h]

end

end GaussianTesting
