module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SO3Rotations
public import GaussianTesting.Kac.SO3EulerAlgebra
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

@[expose] public section

/-!
# Local Euler coordinates for a conjugated axis rotation

The explicit Euler coordinates near the identity justify differentiating
conjugation of one axis subgroup by another. This is the local group-to-Lie-
algebra step used for the finite-dimensional representations in Theorem 4.1.
-/

namespace GaussianTesting.SO3

open Filter
open scoped Topology

noncomputable section

private theorem sin_cos_arctan_div {u v r : ℝ} (hv : 0 < v) (hr : 0 < r)
    (hnorm : u ^ 2 + v ^ 2 = r ^ 2) :
    Real.sin (Real.arctan (u / v)) = u / r ∧
      Real.cos (Real.arctan (u / v)) = v / r := by
  let a := Real.arctan (u / v)
  have hcos : 0 < Real.cos a := Real.cos_arctan_pos _
  have htan : Real.sin a * v = u * Real.cos a := by
    have h := Real.tan_arctan (u / v)
    rw [Real.tan_eq_sin_div_cos] at h
    exact (div_eq_div_iff hcos.ne' hv.ne').mp h
  have hsq : (Real.cos a * r) ^ 2 = v ^ 2 := by
    calc
      (Real.cos a * r) ^ 2 = Real.cos a ^ 2 * (u ^ 2 + v ^ 2) := by rw [hnorm]; ring
      _ = (u * Real.cos a) ^ 2 + (Real.cos a * v) ^ 2 := by ring
      _ = (Real.sin a * v) ^ 2 + (Real.cos a * v) ^ 2 := by rw [htan]
      _ = (Real.sin a ^ 2 + Real.cos a ^ 2) * v ^ 2 := by ring
      _ = v ^ 2 := by rw [Real.sin_sq_add_cos_sq, one_mul]
  have hcv : Real.cos a * r = v := (sq_eq_sq₀ (mul_nonneg hcos.le hr.le) hv.le).mp hsq
  have hc : Real.cos a = v / r := (eq_div_iff hr.ne').mpr hcv
  refine ⟨?_, hc⟩
  apply (eq_div_iff hr.ne').mpr
  have h := congrArg (fun z : ℝ => z * r) htan
  rw [mul_assoc u, hcv] at h
  exact (mul_right_cancel₀ hv.ne') (by nlinarith [h])

/-- First Euler coordinate of `rotX s * rotY t * rotX (-s)` near `t = 0`. -/
def conjugationEulerX (s t : ℝ) : ℝ :=
  Real.arctan ((-Real.sin s * Real.cos s * (1 - Real.cos t)) /
    (Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t))

/-- Second Euler coordinate of the conjugated rotation. -/
def conjugationEulerY (s t : ℝ) : ℝ :=
  Real.arcsin (Real.cos s * Real.sin t)

/-- Third Euler coordinate of the conjugated rotation. -/
def conjugationEulerZ (s t : ℝ) : ℝ :=
  Real.arctan (Real.sin s * Real.sin t / Real.cos t)

@[simp] theorem conjugationEulerX_zero (s : ℝ) : conjugationEulerX s 0 = 0 := by
  simp [conjugationEulerX]

@[simp] theorem conjugationEulerY_zero (s : ℝ) : conjugationEulerY s 0 = 0 := by
  simp [conjugationEulerY]

@[simp] theorem conjugationEulerZ_zero (s : ℝ) : conjugationEulerZ s 0 = 0 := by
  simp [conjugationEulerZ]

theorem hasDerivAt_conjugationEulerX_zero (s : ℝ) :
    HasDerivAt (conjugationEulerX s) 0 0 := by
  change HasDerivAt (fun t => Real.arctan ((-Real.sin s * Real.cos s * (1 - Real.cos t)) /
    (Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t))) 0 0
  have hden : Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos 0 ≠ 0 := by
    simp
  have hd := (((Real.hasDerivAt_cos 0).const_sub 1).const_mul
    (-Real.sin s * Real.cos s)).div
    (((Real.hasDerivAt_cos 0).const_mul (Real.cos s ^ 2)).const_add (Real.sin s ^ 2)) hden
  convert hd.arctan using 1; simp

theorem hasDerivAt_conjugationEulerY_zero (s : ℝ) :
    HasDerivAt (conjugationEulerY s) (Real.cos s) 0 := by
  change HasDerivAt (fun t => Real.arcsin (Real.cos s * Real.sin t)) (Real.cos s) 0
  have hd := ((Real.hasDerivAt_arcsin (x := Real.cos s * Real.sin 0) (by simp) (by simp))).comp 0
    ((Real.hasDerivAt_sin 0).const_mul (Real.cos s))
  convert hd using 1 <;> simp [Function.comp_def]

theorem hasDerivAt_conjugationEulerZ_zero (s : ℝ) :
    HasDerivAt (conjugationEulerZ s) (Real.sin s) 0 := by
  change HasDerivAt (fun t => Real.arctan (Real.sin s * Real.sin t / Real.cos t)) (Real.sin s) 0
  have hd := (((Real.hasDerivAt_sin 0).const_mul (Real.sin s)).div
    (Real.hasDerivAt_cos 0) (by simp)).arctan
  simpa using hd

private theorem conjugationEuler_trig (s t : ℝ)
    (hcos : 0 < Real.cos t)
    (hdiag : 0 < Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t)
    (hsmall : |Real.cos s * Real.sin t| < 1) :
    let r := Real.sqrt (1 - (Real.cos s * Real.sin t) ^ 2)
    0 < r ∧ r ^ 2 = 1 - (Real.cos s * Real.sin t) ^ 2 ∧
      Real.sin (conjugationEulerX s t) = (-Real.sin s * Real.cos s * (1 - Real.cos t)) / r ∧
      Real.cos (conjugationEulerX s t) = (Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t) / r ∧
      Real.sin (conjugationEulerY s t) = Real.cos s * Real.sin t ∧
      Real.cos (conjugationEulerY s t) = r ∧
      Real.sin (conjugationEulerZ s t) = Real.sin s * Real.sin t / r ∧
      Real.cos (conjugationEulerZ s t) = Real.cos t / r := by
  let r := Real.sqrt (1 - (Real.cos s * Real.sin t) ^ 2)
  have hsqpos : 0 < 1 - (Real.cos s * Real.sin t) ^ 2 := by
    rw [abs_lt] at hsmall
    nlinarith
  have hr : 0 < r := Real.sqrt_pos.mpr hsqpos
  have hr2 : r ^ 2 = 1 - (Real.cos s * Real.sin t) ^ 2 := Real.sq_sqrt hsqpos.le
  have hxnorm : (-Real.sin s * Real.cos s * (1 - Real.cos t)) ^ 2 +
      (Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t) ^ 2 = r ^ 2 := by
    rw [hr2]
    linear_combination
      (Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t ^ 2 + 1) * Real.sin_sq_add_cos_sq s +
        Real.cos s ^ 2 * Real.sin_sq_add_cos_sq t
  have hznorm : (Real.sin s * Real.sin t) ^ 2 + Real.cos t ^ 2 = r ^ 2 := by
    rw [hr2]
    linear_combination Real.sin t ^ 2 * Real.sin_sq_add_cos_sq s + Real.sin_sq_add_cos_sq t
  have hx := sin_cos_arctan_div hdiag hr hxnorm
  have hz := sin_cos_arctan_div hcos hr hznorm
  exact ⟨hr, hr2, hx.1, hx.2,
    Real.sin_arcsin (abs_lt.mp hsmall).1.le (abs_lt.mp hsmall).2.le,
    Real.cos_arcsin _, hz.1, hz.2⟩

/-- Near the identity, conjugation of the second-axis subgroup by the
first-axis subgroup has differentiable Euler coordinates. -/
theorem eventually_rotX_rotY_conjugation_factorization (s : ℝ) :
    ∀ᶠ t in 𝓝 (0 : ℝ), rotX s * rotY t * rotX (-s) =
      rotX (conjugationEulerX s t) * rotY (conjugationEulerY s t) *
        rotZ (conjugationEulerZ s t) := by
  have hc : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < Real.cos t :=
    (isOpen_lt continuous_const Real.continuous_cos).mem_nhds (by simp)
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      0 < Real.sin s ^ 2 + Real.cos s ^ 2 * Real.cos t :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp)
  have hs : ∀ᶠ t in 𝓝 (0 : ℝ), |Real.cos s * Real.sin t| < 1 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  filter_upwards [hc, hd, hs] with t hct hdt hst
  obtain ⟨hr, hr2, hax, hcx, hay, hcy, haz, hcz⟩ := conjugationEuler_trig s t hct hdt hst
  exact rotX_rotY_conjugation_factorization s t _ _ _ _ hr.ne' hr2 hax hcx hay hcy haz hcz

end
end GaussianTesting.SO3
