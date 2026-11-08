module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The characteristic-function equation in Proposition 6.1

This is the scalar part of the manuscript proof. The balanced rotation
equation forces positivity by repeated contraction towards zero. Its real
logarithm obeys the parallelogram law, and polarization gives a real bilinear
form by continuity. No moments or differentiability are assumed.
-/

namespace GaussianTesting

open Filter
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The balanced-rotation identity used in Proposition 6.1. -/
def BalancedCharacteristicEquation (χ : E → ℂ) : Prop :=
  ∀ r s, χ r * χ s =
    χ ((Real.sqrt 2)⁻¹ • (r + s)) * χ ((Real.sqrt 2)⁻¹ • (r - s))

private theorem inv_sqrt_two_pos : 0 < (Real.sqrt 2)⁻¹ := by positivity

private theorem inv_sqrt_two_lt_one : (Real.sqrt 2)⁻¹ < 1 := by
  have h : 1 < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  exact inv_lt_one_of_one_lt₀ h

/-- Setting the first variable to zero yields a nonnegative real value. -/
theorem characteristic_rotation_eq_normSq {χ : E → ℂ}
    (hzero : χ 0 = 1) (hneg : ∀ r, χ (-r) = star (χ r))
    (hrot : BalancedCharacteristicEquation χ) (r : E) :
    χ r = (Complex.normSq (χ ((Real.sqrt 2)⁻¹ • r)) : ℂ) := by
  have h := hrot 0 r
  simpa only [hzero, one_mul, zero_add, zero_sub, smul_neg, hneg,
    Complex.star_def, Complex.mul_conj] using h

/-- Continuity and normalization rule out zeros by iterating contraction. -/
theorem characteristic_rotation_ne_zero {χ : E → ℂ}
    (hc : Continuous χ) (hzero : χ 0 = 1)
    (hneg : ∀ r, χ (-r) = star (χ r))
    (hrot : BalancedCharacteristicEquation χ) (r : E) : χ r ≠ 0 := by
  intro hr
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hstep (x : E) (hx : χ x = 0) : χ (c • x) = 0 := by
    have he := characteristic_rotation_eq_normSq hzero hneg hrot x
    rw [hx] at he
    have hn : Complex.normSq (χ (c • x)) = 0 := by exact_mod_cast he.symm
    exact Complex.normSq_eq_zero.mp hn
  have hn (n : ℕ) : χ (c ^ n • r) = 0 := by
    induction n with
    | zero => simpa using hr
    | succ n ih => simpa only [pow_succ', mul_smul] using hstep (c ^ n • r) ih
  have ht : Tendsto (fun n : ℕ => c ^ n • r) atTop (𝓝 (0 : E)) := by
    simpa only [zero_smul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one inv_sqrt_two_pos.le
        inv_sqrt_two_lt_one).smul_const r
  have hc0 := hc.continuousAt.tendsto.comp ht
  simp only [Function.comp_def, hn, hzero] at hc0
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hc0)

/-- The characteristic function is strictly positive and real everywhere. -/
theorem characteristic_rotation_positive {χ : E → ℂ}
    (hc : Continuous χ) (hzero : χ 0 = 1)
    (hneg : ∀ r, χ (-r) = star (χ r))
    (hrot : BalancedCharacteristicEquation χ) (r : E) :
    0 < (χ r).re ∧ (χ r).im = 0 := by
  rw [characteristic_rotation_eq_normSq hzero hneg hrot r]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  exact Complex.normSq_pos.mpr (characteristic_rotation_ne_zero hc hzero hneg hrot _)

/-- Polarization of a real function, with the manuscript's factor `1/4`. -/
def realPolarization (f : E → ℝ) (r s : E) : ℝ := (f (r+s) - f (r-s)) / 4

private theorem polarization_add_left {f : E → ℝ}
    (hpar : ∀ x y, f (x+y) + f (x-y) = 2*f x + 2*f y) (x y z : E) :
    realPolarization f (x+y) z = realPolarization f x z + realPolarization f y z := by
  have h1 := hpar (x+y+z) (x-z)
  have h2 := hpar (x+y-z) (x+z)
  have h3 := hpar (y+z) z
  have h4 := hpar (y-z) z
  unfold realPolarization
  module_nf with ℝ at h1 h2 h3 h4 ⊢
  linear_combination (-h1+h2+h3-h4)/8

omit [NormedSpace ℝ E] in
private theorem polarization_symm {f : E → ℝ} (hzero : f 0 = 0)
    (hpar : ∀ x y, f (x+y) + f (x-y) = 2*f x + 2*f y) (x y : E) :
    realPolarization f x y = realPolarization f y x := by
  have heven (z : E) : f (-z) = f z := by
    have h := hpar 0 z
    simp only [zero_add, zero_sub, hzero, mul_zero, zero_add] at h
    linarith
  unfold realPolarization
  rw [add_comm x y, ← neg_sub y x, heven]

/-- Continuous solutions of the parallelogram equation are quadratic,
with the manuscript's polarization as their symmetric bilinear form. -/
theorem exists_bilinear_of_continuous_parallelogram {f : E → ℝ}
    (hc : Continuous f) (hzero : f 0 = 0)
    (hpar : ∀ x y, f (x+y) + f (x-y) = 2*f x + 2*f y) :
    ∃ B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ,
      (∀ x y, B x y = realPolarization f x y) ∧
      Continuous (fun p : E × E => B p.1 p.2) ∧
      (∀ x, B x x = f x) := by
  have hs := polarization_symm hzero hpar
  have hcont (y : E) : Continuous (fun x => realPolarization f x y) :=
    ((hc.comp (continuous_id.add continuous_const)).sub
      (hc.comp (continuous_id.sub continuous_const))).div_const 4
  let L (y : E) : E →L[ℝ] ℝ :=
    (AddMonoidHom.mk' (fun x => realPolarization f x y)
      (fun x z => polarization_add_left hpar x z y)).toRealLinearMap (hcont y)
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    { toFun := fun x => (L x).toLinearMap
      map_add' := by
        intro x y
        ext z
        change realPolarization f z (x+y) =
          realPolarization f z x + realPolarization f z y
        rw [hs z (x+y), hs z x, hs z y]
        exact polarization_add_left hpar x y z
      map_smul' := by
        intro a x
        ext z
        change realPolarization f z (a • x) = a * realPolarization f z x
        rw [hs z (a • x), hs z x]
        exact (L z).map_smul a x }
  have hB (x y : E) : B x y = realPolarization f x y := hs y x
  refine ⟨B, hB, ?_, ?_⟩
  · simp_rw [hB]
    exact ((hc.comp (continuous_fst.add continuous_snd)).sub
      (hc.comp (continuous_fst.sub continuous_snd))).div_const 4
  · intro x
    rw [hB]
    have h := hpar x x
    simp only [sub_self, hzero] at h
    unfold realPolarization
    rw [sub_self, hzero]
    linarith

/-- The real logarithm of the rotation-invariant characteristic function
obeys the parallelogram equation. -/
theorem characteristic_rotation_log_parallelogram {χ : E → ℂ}
    (hc : Continuous χ) (hzero : χ 0 = 1)
    (hneg : ∀ r, χ (-r) = star (χ r))
    (hrot : BalancedCharacteristicEquation χ) :
    ∀ r s, Real.log (χ (r+s)).re + Real.log (χ (r-s)).re =
      2 * Real.log (χ r).re + 2 * Real.log (χ s).re := by
  have hp := characteristic_rotation_positive hc hzero hneg hrot
  have hr (r s : E) : (χ r).re * (χ s).re =
      (χ ((Real.sqrt 2)⁻¹ • (r+s))).re *
        (χ ((Real.sqrt 2)⁻¹ • (r-s))).re := by
    have h := congrArg Complex.re (hrot r s)
    simpa only [Complex.mul_re, (hp _).2, mul_zero, sub_zero] using h
  have hl (r s : E) : Real.log (χ r).re + Real.log (χ s).re =
      Real.log (χ ((Real.sqrt 2)⁻¹ • (r+s))).re +
        Real.log (χ ((Real.sqrt 2)⁻¹ • (r-s))).re := by
    rw [← Real.log_mul (hp _).1.ne' (hp _).1.ne', hr,
      Real.log_mul (hp _).1.ne' (hp _).1.ne']
  have hscale (r : E) : Real.log (χ r).re =
      2 * Real.log (χ ((Real.sqrt 2)⁻¹ • r)).re := by
    have h := hl r 0
    simp only [hzero, Complex.one_re, Real.log_one, add_zero, sub_zero] at h
    linarith
  intro r s
  have h := hl r s
  rw [hscale (r+s), hscale (r-s)]
  linarith

/-- The scalar conclusion in Proposition 6.1: the characteristic function
is the exponential of a continuous real quadratic form. -/
theorem characteristic_rotation_eq_exp_quadratic {χ : E → ℂ}
    (hc : Continuous χ) (hzero : χ 0 = 1)
    (hneg : ∀ r, χ (-r) = star (χ r))
    (hrot : BalancedCharacteristicEquation χ) :
    ∃ Q : QuadraticForm ℝ E, Continuous Q ∧
      (∀ r, χ r = (Real.exp (Q r) : ℂ)) := by
  have hp := characteristic_rotation_positive hc hzero hneg hrot
  let f (r : E) := Real.log (χ r).re
  have hfc : Continuous f := (Complex.continuous_re.comp hc).log (fun r => (hp r).1.ne')
  have hfzero : f 0 = 0 := by simp [f, hzero]
  obtain ⟨B, _, hBc, hdiag⟩ := exists_bilinear_of_continuous_parallelogram
    hfc hfzero (characteristic_rotation_log_parallelogram hc hzero hneg hrot)
  refine ⟨LinearMap.BilinMap.toQuadraticMap B,
    hBc.comp (continuous_id.prodMk continuous_id), ?_⟩
  intro r
  change χ r = (Real.exp (B r r) : ℂ)
  rw [hdiag, Real.exp_log (hp r).1]
  exact Complex.ext rfl (hp r).2

/-- For a bounded characteristic function, the quadratic exponent is
nonpositive, as required for a centered Gaussian characteristic function. -/
theorem characteristic_rotation_eq_exp_nonpos_quadratic {χ : E → ℂ}
    (hc : Continuous χ) (hzero : χ 0 = 1)
    (hneg : ∀ r, χ (-r) = star (χ r))
    (hbound : ∀ r, ‖χ r‖ ≤ 1)
    (hrot : BalancedCharacteristicEquation χ) :
    ∃ Q : QuadraticForm ℝ E, Continuous Q ∧
      (∀ r, Q r ≤ 0) ∧ (∀ r, χ r = (Real.exp (Q r) : ℂ)) := by
  obtain ⟨Q, hQc, hQ⟩ := characteristic_rotation_eq_exp_quadratic hc hzero hneg hrot
  refine ⟨Q, hQc, ?_, hQ⟩
  intro r
  have h := hbound r
  rw [hQ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
  exact Real.exp_le_one_iff.mp h

end
end GaussianTesting
