module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.CoherentCharacteristicEquation
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Nondegeneracy of physical Gaussian characteristic functions

The Weyl relations and strong continuity rule out eigenvectors of a nontrivial
Weyl displacement. Consequently a unit wavefunction has characteristic-function
modulus strictly less than one away from the origin. In particular, a Gaussian
characteristic function of an actual pure state has a strictly negative
quadratic exponent; no nonsingularity or moment hypothesis is assumed.
-/

namespace GaussianTesting

open scoped InnerProductSpace Topology

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 600000

attribute [local irreducible] weylOperator

/-- Scaling a wavefunction scales its Weyl characteristic function by the
squared modulus of the scalar. -/
theorem pureWaveCharacteristic_smul (m : ℕ) (f : WaveSpace m) (z : ℂ) (r : WavePhase m) :
    pureWaveCharacteristic m (z • f) r = (‖z‖ ^ 2 : ℝ) * pureWaveCharacteristic m f r := by
  unfold pureWaveCharacteristic
  rw [map_smul, inner_smul_left, inner_smul_right]
  change star z * (z * _) = _
  rw [← mul_assoc, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

/-- Real bilinearity in the second variable of the manuscript's symplectic form. -/
theorem waveSymplectic_smul_right {m : ℕ} (r s : WavePhase m) (t : ℝ) :
    waveSymplectic r (t • s) = t * waveSymplectic r s := by
  simp only [waveSymplectic, Prod.smul_fst, Prod.smul_snd, inner_smul_right]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem zero_of_exp_linear_eventually_one (a : ℝ)
    (h : (fun t : ℝ => Complex.exp (Complex.I * (t * a : ℝ))) =ᶠ[𝓝 0] fun _ => 1) :
    a = 0 := by
  have hlin : HasDerivAt (fun t : ℝ => Complex.I * (t * a : ℝ))
      (Complex.I * (a : ℂ)) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp.const_mul Complex.I)
      using 1; simp
  have he := hlin.cexp
  have hc := (hasDerivAt_const (0 : ℝ) (1 : ℂ)).congr_of_eventuallyEq h
  have hz : Complex.I * (a : ℂ) = 0 := by
    simpa only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      using he.unique hc
  exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero)

/-- A nontrivial Weyl displacement has no unit-vector eigenstate in the actual
Schrödinger representation. -/
theorem weylOperator_parameter_zero_of_eigenvector {m : ℕ} (f : WaveSpace m)
    (hf : ‖f‖ = 1) (r : WavePhase m) (z : ℂ)
    (heigen : weylOperator m r f = z • f) : r = 0 := by
  have hz : ‖z‖ = 1 := by
    have h := congrArg norm heigen
    simpa only [weylOperator_norm, norm_smul, hf, mul_one] using h.symm
  have hphase (s : WavePhase m) :
      Complex.exp (Complex.I * (waveSymplectic r s : ℂ)) *
        pureWaveCharacteristic m f s = pureWaveCharacteristic m f s := by
    have h := pureWaveCharacteristic_displacement m r s f
    rw [heigen, pureWaveCharacteristic_smul, hz] at h
    simpa only [one_pow, Complex.ofReal_one, one_mul] using h.symm
  have hform (s : WavePhase m) : waveSymplectic r s = 0 := by
    apply zero_of_exp_linear_eventually_one
    have hcont : Continuous (fun t : ℝ => pureWaveCharacteristic m f (t • s)) :=
      (continuous_pureWaveCharacteristic m f).comp (continuous_id.smul continuous_const)
    have hnonzero : pureWaveCharacteristic m f ((0 : ℝ) • s) ≠ 0 := by
      simp only [zero_smul, pureWaveCharacteristic_zero, hf, one_pow, Complex.ofReal_one]
      exact one_ne_zero
    filter_upwards [hcont.continuousAt.eventually_ne hnonzero] with t ht
    have h := hphase (t • s)
    rw [waveSymplectic_smul_right] at h
    exact mul_right_cancel₀ ht (h.trans (one_mul _).symm)
  have hsum := hform (-r.2, r.1)
  change inner ℝ r.1 r.1 - inner ℝ r.2 (-r.2) = 0 at hsum
  rw [inner_neg_right, sub_neg_eq_add, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hsum
  have hq : r.1 = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖r.2‖, norm_nonneg r.1])
  have hp : r.2 = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖r.1‖, norm_nonneg r.2])
  exact Prod.ext hq hp

/-- The modulus of a unit state's characteristic function is strictly less
than one at every nonzero phase-space displacement. -/
theorem norm_pureWaveCharacteristic_lt_one {m : ℕ} (f : WaveSpace m) (hf : ‖f‖ = 1)
    (r : WavePhase m) (hr : r ≠ 0) : ‖pureWaveCharacteristic m f r‖ < 1 := by
  have hle : ‖pureWaveCharacteristic m f r‖ ≤ 1 := by
    simpa only [hf, one_pow] using norm_pureWaveCharacteristic_le m f r
  apply lt_of_le_of_ne hle
  intro h
  have hf0 : f ≠ 0 := by intro hz; simp only [hz, norm_zero, zero_ne_one] at hf
  have hD0 : weylOperator m r f ≠ 0 := by
    intro hz
    have hnorm := congrArg norm hz
    simp only [weylOperator_norm, hf, norm_zero, one_ne_zero] at hnorm
  have heq : ‖inner ℂ f (weylOperator m r f)‖ = ‖f‖ * ‖weylOperator m r f‖ := by
    simpa only [pureWaveCharacteristic, weylOperator_norm, hf, one_mul] using h
  obtain ⟨z, _, heigen⟩ := (norm_inner_eq_norm_iff hf0 hD0).mp heq
  exact hr (weylOperator_parameter_zero_of_eigenvector f hf r z heigen)

/-- The Gaussian quadratic exponent of a physical unit pure state is strictly
negative away from zero, even if the original Gaussian formula did not assert it. -/
theorem gaussianCharacteristic_exponent_neg {m : ℕ} (f : WaveSpace m) (hf : ‖f‖ = 1)
    (Q : QuadraticForm ℝ (WavePhase m)) (L : WavePhase m →L[ℝ] ℝ)
    (hχ : ∀ r, pureWaveCharacteristic m f r =
      Complex.exp ((Q r : ℂ) + Complex.I * (L r : ℂ)))
    (r : WavePhase m) (hr : r ≠ 0) : Q r < 0 := by
  have h := norm_pureWaveCharacteristic_lt_one f hf r hr
  rw [hχ, Complex.norm_exp] at h
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Real.exp_lt_one_iff] using h

/-- Negating the real exponent gives a positive-definite quadratic form on
all of phase space, hence also on either coordinate block. -/
theorem gaussianCharacteristic_neg_posDef {m : ℕ} (f : WaveSpace m) (hf : ‖f‖ = 1)
    (Q : QuadraticForm ℝ (WavePhase m)) (L : WavePhase m →L[ℝ] ℝ)
    (hχ : ∀ r, pureWaveCharacteristic m f r =
      Complex.exp ((Q r : ℂ) + Complex.I * (L r : ℂ))) : (-Q).PosDef := by
  intro r hr
  exact neg_pos.mpr (gaussianCharacteristic_exponent_neg f hf Q L hχ r hr)

/-- A Weyl displacement removes precisely the linear phase of a Gaussian
characteristic function, preserving the unit norm. -/
theorem gaussianCharacteristic_centered_by_displacement {m : ℕ}
    (f : WaveSpace m) (hf : ‖f‖ = 1)
    (Q : QuadraticForm ℝ (WavePhase m)) (L : WavePhase m →L[ℝ] ℝ)
    (hχ : ∀ r, pureWaveCharacteristic m f r =
      Complex.exp ((Q r : ℂ) + Complex.I * (L r : ℂ))) :
    ∃ a : WavePhase m, ‖weylOperator m (-a) f‖ = 1 ∧
      ∀ r, pureWaveCharacteristic m (weylOperator m (-a) f) r = (Real.exp (Q r) : ℂ) := by
  obtain ⟨a, ha⟩ := exists_waveSymplectic_eq_linear L
  refine ⟨a, (weylOperator_norm m (-a) f).trans hf, fun r => ?_⟩
  rw [pureWaveCharacteristic_displacement, waveSymplectic_neg_left, ha, hχ,
    ← Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_exp]
  congr 1
  ring

end
end GaussianTesting
