module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerVacuum
public import GaussianTesting.Bosons.PureCharacteristic

@[expose] public section

/-!
# The Gaussian characteristic function of the vacuum

The explicit Schrödinger vacuum and Weyl action give
`⟪0, D_(q,p) 0⟫ = exp(-(‖q‖² + ‖p‖²)/4)` by the Gaussian Fourier integral.
This proof uses actual `L²` wavefunctions, independently of a number-basis
identification.
-/

namespace GaussianTesting

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

private theorem vacuum_exponent (m : ℕ) (q p x : WaveConfig m) :
    ((-‖x‖ ^ 2 / 2 : ℝ) : ℂ) +
        Complex.I * ((inner ℝ p x - inner ℝ p q / 2 : ℝ) : ℂ) +
        ((-‖x-q‖ ^ 2 / 2 : ℝ) : ℂ) =
      ((-‖q‖ ^ 2 / 4 : ℝ) : ℂ) +
        (((-‖x - (1/2 : ℝ) • q‖ ^ 2 : ℝ) : ℂ) +
          Complex.I * (inner ℝ p (x - (1/2 : ℝ) • q) : ℂ)) := by
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_right, inner_smul_right]
  push_cast
  ring

private theorem vacuum_integrand (m : ℕ) (q p x : WaveConfig m) :
    star (waveVacuumFun m x) *
      (weylPhase (q,p) x * waveVacuumFun m (x-q)) =
    (((Real.pi ^ (-(m : ℝ) / 4)) ^ 2 : ℝ) : ℂ) *
      Complex.exp ((-‖q‖ ^ 2 / 4 : ℝ) : ℂ) *
      Complex.exp (((-‖x - (1/2 : ℝ) • q‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * (inner ℝ p (x - (1/2 : ℝ) • q) : ℂ)) := by
  simp only [waveVacuumFun, weylPhase, star_mul, Complex.star_def,
    ← Complex.exp_conj, Complex.conj_ofReal, Complex.ofReal_exp]
  have h := congrArg Complex.exp (vacuum_exponent m q p x)
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_add] at h
  simp only [Complex.ofReal_pow]
  calc
    _ = ((Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ) ^ 2 *
        (Complex.exp ((-‖x‖ ^ 2 / 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((inner ℝ p x - inner ℝ p q / 2 : ℝ) : ℂ)) *
          Complex.exp ((-‖x-q‖ ^ 2 / 2 : ℝ) : ℂ)) := by ring
    _ = _ := by rw [h]; ring

private theorem vacuum_normalization (m : ℕ) :
    (((Real.pi ^ (-(m : ℝ) / 4)) ^ 2 : ℝ) : ℂ) *
      (Real.pi : ℂ) ^ ((m : ℂ) / 2) = 1 := by
  have hp : (Real.pi : ℂ) ^ ((m : ℂ) / 2) =
      ((Real.pi ^ ((m : ℝ) / 2) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
      using (Complex.ofReal_cpow Real.pi_pos.le ((m : ℝ) / 2)).symm
  rw [hp, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_one, Complex.ofReal_inj]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul Real.pi_pos.le,
    ← Real.rpow_add Real.pi_pos]
  rw [show -(m : ℝ) / 4 * (2 : ℕ) + (m : ℝ) / 2 = 0 by push_cast; ring,
    Real.rpow_zero]

/-- The characteristic function of the oscillator vacuum is the centered
Gaussian `exp(-(‖q‖² + ‖p‖²)/4)`. -/
theorem inner_waveVacuum_weylOperator (m : ℕ) (r : WavePhase m) :
    inner ℂ (waveVacuum m) (weylOperator m r (waveVacuum m)) =
      ((Real.exp (-(‖r.1‖ ^ 2 + ‖r.2‖ ^ 2) / 4) : ℝ) : ℂ) := by
  rcases r with ⟨q,p⟩
  let C : ℂ := (((Real.pi ^ (-(m : ℝ) / 4)) ^ 2 : ℝ) : ℂ)
  let G : WaveConfig m → ℂ := fun x =>
    Complex.exp (((-‖x‖ ^ 2 : ℝ) : ℂ) + Complex.I * (inner ℝ p x : ℂ))
  rw [L2.inner_def]
  calc
    (∫ x, inner ℂ (waveVacuum m x) (weylOperator m (q,p) (waveVacuum m) x)) =
        ∫ x, C * Complex.exp ((-‖q‖ ^ 2 / 4 : ℝ) : ℂ) *
          G (x - (1/2 : ℝ) • q) := by
      apply integral_congr_ae
      filter_upwards [waveVacuum_coeFn m,
        weylOperator_coeFn m (q,p) (waveVacuum m),
        (waveTranslation_measurePreserving q).quasiMeasurePreserving.ae_eq_comp
          (waveVacuum_coeFn m)] with x hx hD hshift
      simp only [Function.comp_apply] at hshift
      rw [hx, hD, hshift, RCLike.inner_apply, mul_comm]
      exact vacuum_integrand m q p x
    _ = C * Complex.exp ((-‖q‖ ^ 2 / 4 : ℝ) : ℂ) * ∫ x, G x := by
      rw [integral_const_mul, integral_sub_right_eq_self]
    _ = C * Complex.exp ((-‖q‖ ^ 2 / 4 : ℝ) : ℂ) *
        ((Real.pi : ℂ) ^ ((m : ℂ) / 2) *
          Complex.exp ((-‖p‖ ^ 2 / 4 : ℝ) : ℂ)) := by
      congr 1
      simpa only [G, Complex.ofReal_neg, Complex.ofReal_pow,
        neg_one_mul, div_one, finrank_euclideanSpace_fin,
        Complex.I_sq, mul_one, Complex.ofReal_div, Complex.ofReal_ofNat]
        using GaussianFourier.integral_cexp_neg_mul_sq_norm_add
          (V := WaveConfig m) (b := 1) (by norm_num) Complex.I p
    _ = Complex.exp ((-‖q‖ ^ 2 / 4 : ℝ) : ℂ) *
        Complex.exp ((-‖p‖ ^ 2 / 4 : ℝ) : ℂ) := by
      calc
        _ = (C * (Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
            (Complex.exp ((-‖q‖ ^ 2 / 4 : ℝ) : ℂ) *
              Complex.exp ((-‖p‖ ^ 2 / 4 : ℝ) : ℂ)) := by ring
        _ = _ := by rw [show C * (Real.pi : ℂ) ^ ((m : ℂ) / 2) = 1 from
          vacuum_normalization m, one_mul]
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.ofReal_add, ← Complex.ofReal_exp]
      congr 2
      dsimp
      ring

/-- The vacuum characteristic function `η` used in Proposition 6.3. -/
def vacuumCharacteristic {m : ℕ} (r : WavePhase m) : ℂ :=
  Real.exp (-(‖r.1‖ ^ 2 + ‖r.2‖ ^ 2) / 4)

@[simp] theorem pureWaveCharacteristic_vacuum (m : ℕ) (r : WavePhase m) :
    pureWaveCharacteristic m (waveVacuum m) r = vacuumCharacteristic r :=
  inner_waveVacuum_weylOperator m r

/-- The same formula in the manuscript's density-operator trace notation. -/
theorem waveCharacteristic_vacuum {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (r : WavePhase m) :
    waveCharacteristic b (waveVacuumProjection m) r = vacuumCharacteristic r := by
  exact (waveCharacteristic_rankOne b (waveVacuum m) r).trans
    (pureWaveCharacteristic_vacuum m r)

/-- The vacuum characteristic function never vanishes. -/
theorem vacuumCharacteristic_ne_zero {m : ℕ} (r : WavePhase m) :
    vacuumCharacteristic r ≠ 0 := by
  unfold vacuumCharacteristic
  exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

@[simp] theorem vacuumCharacteristic_zero (m : ℕ) :
    vacuumCharacteristic (0 : WavePhase m) = 1 := by
  simp [vacuumCharacteristic]

@[simp] theorem vacuumCharacteristic_neg {m : ℕ} (r : WavePhase m) :
    vacuumCharacteristic (-r) = vacuumCharacteristic r := by
  simp [vacuumCharacteristic]

/-- A displaced vacuum has the Gaussian characteristic function times the
linear character specified by its displacement. -/
theorem pureWaveCharacteristic_displaced_vacuum (m : ℕ) (a r : WavePhase m) :
    pureWaveCharacteristic m (weylOperator m a (waveVacuum m)) r =
      Complex.exp (Complex.I * (waveSymplectic a r : ℂ)) * vacuumCharacteristic r := by
  rw [pureWaveCharacteristic_displacement, pureWaveCharacteristic_vacuum]

private theorem norm_inv_sqrt_two_smul_sq {m : ℕ} (x : WaveConfig m) :
    ‖(Real.sqrt 2)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The balanced-rotation product identity for `η` used when normalizing the
characteristic functions in Proposition 6.3. -/
theorem vacuumCharacteristic_balanced {m : ℕ} (r s : WavePhase m) :
    vacuumCharacteristic r * vacuumCharacteristic s =
      vacuumCharacteristic ((Real.sqrt 2)⁻¹ • (r+s)) *
        vacuumCharacteristic ((Real.sqrt 2)⁻¹ • (r-s)) := by
  simp only [vacuumCharacteristic, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
    norm_inv_sqrt_two_smul_sq, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  simp only [norm_add_sq_real, norm_sub_sq_real]
  ring

end
end GaussianTesting
