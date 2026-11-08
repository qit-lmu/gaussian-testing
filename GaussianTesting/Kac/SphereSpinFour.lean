module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereKacTransition
public import GaussianTesting.Kac.SphereSupport
public import GaussianTesting.Kac.SphereTransitivity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The spin-four eigenvector of the spherical Kac operator

The degree-four axial zonal functions realize the three vectors in the
manuscript's spin-four calculation. Averaging about a different coordinate
axis multiplies the corresponding zonal function by `a₄ = 3/8`. Their sum
therefore has Kac eigenvalue `7/12`.
-/

namespace GaussianTesting.SO3

open intervalIntegral Real

noncomputable section

private theorem circle_integral_square (u v : ℝ) :
    (∫ θ in 0..2 * Real.pi, (u * Real.cos θ + v * Real.sin θ) ^ 2) =
      Real.pi * (u ^ 2 + v ^ 2) := by
  have he : (fun θ => (u * Real.cos θ + v * Real.sin θ) ^ 2) =
      fun θ => u ^ 2 * Real.cos θ ^ 2 +
        (2 * u * v) * (Real.sin θ * Real.cos θ) + v ^ 2 * Real.sin θ ^ 2 := by
    funext θ
    ring
  rw [he, integral_add, integral_add] <;>
    try (apply Continuous.intervalIntegrable; fun_prop)
  simp only [integral_const_mul, integral_cos_sq, integral_sin_mul_cos₁, integral_sin_sq,
    Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]
  ring

private theorem circle_integral_fourth (u v : ℝ) :
    (∫ θ in 0..2 * Real.pi, (u * Real.cos θ + v * Real.sin θ) ^ 4) =
      (3 * Real.pi / 4) * (u ^ 2 + v ^ 2) ^ 2 := by
  have hc : (∫ θ in 0..2 * Real.pi, Real.cos θ ^ 4) = 3 * Real.pi / 4 := by
    have h := @integral_cos_pow 0 (2 * Real.pi) 2
    norm_num at h
    linarith
  have hs : (∫ θ in 0..2 * Real.pi, Real.sin θ ^ 4) = 3 * Real.pi / 4 := by
    have h := @integral_sin_pow 0 (2 * Real.pi) 2
    norm_num at h
    linarith
  have h13 : (∫ θ in 0..2 * Real.pi, Real.sin θ * Real.cos θ ^ 3) = 0 := by
    simpa using (@integral_sin_pow_odd_mul_cos_pow 0 (2 * Real.pi) 0 3)
  have h31 : (∫ θ in 0..2 * Real.pi, Real.sin θ ^ 3 * Real.cos θ) = 0 := by
    simpa using (@integral_sin_pow_mul_cos_pow_odd 0 (2 * Real.pi) 3 0)
  have h22 : (∫ θ in 0..2 * Real.pi, Real.sin θ ^ 2 * Real.cos θ ^ 2) =
      Real.pi / 4 := by
    rw [integral_sin_sq_mul_cos_sq]
    have h8 : Real.sin (4 * (2 * Real.pi)) = 0 := by
      convert Real.sin_nat_mul_pi 8 using 1
      congr 1
      ring
    rw [h8]
    simp
    ring
  have he : (fun θ => (u * Real.cos θ + v * Real.sin θ) ^ 4) = fun θ =>
      u ^ 4 * Real.cos θ ^ 4 +
      (4 * u ^ 3 * v) * (Real.sin θ * Real.cos θ ^ 3) +
      (6 * u ^ 2 * v ^ 2) * (Real.sin θ ^ 2 * Real.cos θ ^ 2) +
      (4 * u * v ^ 3) * (Real.sin θ ^ 3 * Real.cos θ) +
      v ^ 4 * Real.sin θ ^ 4 := by
    funext θ
    ring
  rw [he, integral_add, integral_add, integral_add, integral_add] <;>
    try (apply Continuous.intervalIntegrable; fun_prop)
  simp only [integral_const_mul, hc, hs, h13, h31, h22]
  ring

private theorem circle_average_zonalFour (u v w : ℝ) (huvw : u ^ 2 + v ^ 2 + w ^ 2 = 1) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in 0..2 * Real.pi,
        (35 * (u * Real.cos θ + v * Real.sin θ) ^ 4 -
          30 * (u * Real.cos θ + v * Real.sin θ) ^ 2 + 3) / 8) =
      (3 / 8 : ℝ) * ((35 * w ^ 4 - 30 * w ^ 2 + 3) / 8) := by
  rw [integral_div, integral_add, integral_sub] <;>
    try (apply Continuous.intervalIntegrable; fun_prop)
  rw [integral_const_mul, integral_const_mul, circle_integral_fourth, circle_integral_square,
    integral_const]
  have he : u ^ 2 + v ^ 2 = 1 - w ^ 2 := by linarith
  rw [he]
  simp only [sub_zero, smul_eq_mul]
  field_simp
  ring

/-- The degree-four zonal spherical harmonic about coordinate axis `a`, with value one at
the corresponding pole. Its spherical restriction is the Legendre polynomial `P₄(xₐ)`. -/
def sphereZonalFour (a : Fin 3) : C(Sphere, ℂ) :=
  ⟨fun x => (((35 * (x : SphereAmbient) a ^ 4 - 30 * (x : SphereAmbient) a ^ 2 + 3) / 8 : ℝ) : ℂ), by
    have hc : Continuous (fun x : Sphere => (x : SphereAmbient) a) :=
      (PiLp.continuous_apply 2 _ a).comp continuous_subtype_val
    fun_prop⟩

@[simp] theorem sphereZonalFour_apply (a : Fin 3) (x : Sphere) :
    sphereZonalFour a x =
      (((35 * (x : SphereAmbient) a ^ 4 - 30 * (x : SphereAmbient) a ^ 2 + 3) / 8 : ℝ) : ℂ) := rfl

private theorem sphereZonalFour_axisAverage_apply (b a : Fin 3) (x : Sphere) :
    sphereAxisContinuousAverage b (sphereZonalFour a) x =
      (((2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi,
        (35 * (sphereRotation (axisRotation b θ) x : SphereAmbient) a ^ 4 -
          30 * (sphereRotation (axisRotation b θ) x : SphereAmbient) a ^ 2 + 3) / 8) : ℝ) : ℂ) := by
  rw [sphereAxisContinuousAverage_apply]
  simp only [sphereZonalFour_apply, intervalIntegral.integral_ofReal]
  simp [Complex.real_smul]

private def axisCoordinatePartner (b a : Fin 3) (x : Sphere) : ℝ :=
  ![![0, -(x : SphereAmbient) 2, (x : SphereAmbient) 1],
    ![(x : SphereAmbient) 2, 0, -(x : SphereAmbient) 0],
    ![-(x : SphereAmbient) 1, (x : SphereAmbient) 0, 0]] b a

private theorem axisRotation_fixed_coordinate (b : Fin 3) (θ : ℝ) (x : Sphere) :
    (sphereRotation (axisRotation b θ) x : SphereAmbient) b = (x : SphereAmbient) b := by
  simp only [sphereRotation_coe, rotationEquiv_apply]
  fin_cases b <;> simp [axisRotation, rotX, rotY, rotZ, rotXMatrix, rotYMatrix, rotZMatrix,
    Fin.sum_univ_three]

private theorem axisRotation_other_coordinate (b a : Fin 3) (hab : a ≠ b)
    (θ : ℝ) (x : Sphere) :
    (sphereRotation (axisRotation b θ) x : SphereAmbient) a =
      (x : SphereAmbient) a * Real.cos θ + axisCoordinatePartner b a x * Real.sin θ := by
  simp only [sphereRotation_coe, rotationEquiv_apply]
  fin_cases b <;> fin_cases a <;>
    simp_all [axisRotation, rotX, rotY, rotZ, rotXMatrix, rotYMatrix, rotZMatrix,
      axisCoordinatePartner, Fin.sum_univ_three] <;> ring

private theorem axisCoordinatePartner_squares (b a : Fin 3) (hab : a ≠ b) (x : Sphere) :
    (x : SphereAmbient) a ^ 2 + axisCoordinatePartner b a x ^ 2 +
      (x : SphereAmbient) b ^ 2 = 1 := by
  have hn : ‖(x : SphereAmbient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hs := congrArg (fun t : ℝ => t ^ 2) hn
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, one_pow] at hs
  fin_cases b <;> fin_cases a <;> simp_all [axisCoordinatePartner] <;> nlinarith

/-- The three axial degree-four functions have the manuscript's projection coefficient
`a₄ = 3/8` between different axes. -/
theorem sphereAxisContinuousAverage_zonalFour (b a : Fin 3) :
    sphereAxisContinuousAverage b (sphereZonalFour a) =
      (if a = b then (1 : ℂ) else 3 / 8) • sphereZonalFour b := by
  ext x
  rw [sphereZonalFour_axisAverage_apply]
  by_cases hab : a = b
  · subst a
    simp only [axisRotation_fixed_coordinate, integral_const, sub_zero, smul_eq_mul]
    simp only [ite_true, one_smul, sphereZonalFour_apply]
    congr 1
    field_simp
  · simp_rw [axisRotation_other_coordinate b a hab]
    rw [circle_average_zonalFour _ _ _ (axisCoordinatePartner_squares b a hab x)]
    simp [hab, sphereZonalFour_apply, Complex.ofReal_mul]

/-- The sum of the three axial spin-four functions is the eigenvector represented
by `(1,1,1)` in the manuscript's three-by-three matrix. -/
def sphereSpinFour : C(Sphere, ℂ) := ∑ a : Fin 3, sphereZonalFour a

/-- Averaging the sum about one axis gives `1 + 2a₄ = 7/4` times its zonal function. -/
theorem sphereAxisContinuousAverage_spinFour (b : Fin 3) :
    sphereAxisContinuousAverage b sphereSpinFour = (7 / 4 : ℂ) • sphereZonalFour b := by
  apply sphereContinuousToLp_injective
  rw [sphereContinuousToLp_axisAverage, map_smul]
  change axisCircleAverageCLM sphereRepresentation continuous_sphereRepresentation_orbit b
    (sphereContinuousToLp sphereSpinFour) = _
  simp only [sphereSpinFour, map_sum]
  change (∑ a : Fin 3, axisCircleAverage sphereRepresentation b
    (sphereContinuousToLp (sphereZonalFour a))) = _
  simp_rw [← sphereContinuousToLp_axisAverage, sphereAxisContinuousAverage_zonalFour, map_smul]
  fin_cases b <;> simp [Fin.sum_univ_three] <;> module

/-- The manuscript's spin-four eigenvalue `7/12` in the concrete spherical realization. -/
theorem sphereContinuousTransition_spinFour :
    sphereContinuousTransition sphereSpinFour = (7 / 12 : ℂ) • sphereSpinFour := by
  simp only [sphereContinuousTransition, sphereAxisContinuousAverage_spinFour]
  simp only [sphereSpinFour, Fin.sum_univ_three]
  module

/-- The same spin-four eigenvector identity in `L²(S²)`. -/
theorem sphereKacTransition_spinFour :
    sphereKacTransition (sphereContinuousToLp sphereSpinFour) =
      (7 / 12 : ℂ) • sphereContinuousToLp sphereSpinFour := by
  rw [sphereKacTransition_continuous, sphereContinuousTransition_spinFour, map_smul]

/-- The spin-four witness is nonzero already at the first coordinate pole. -/
theorem sphereSpinFour_pole : sphereSpinFour spherePole = 7 / 4 := by
  norm_num [sphereSpinFour, Fin.sum_univ_three, sphereZonalFour, spherePole, PiLp.single_apply]

/-- The spin-four eigenvector is a nonzero L² vector. -/
theorem sphereSpinFour_toLp_ne_zero : sphereContinuousToLp sphereSpinFour ≠ 0 :=
  sphereContinuousToLp_ne_zero_of_apply_ne_zero sphereSpinFour spherePole (by
    rw [sphereSpinFour_pole]
    norm_num)

end
end GaussianTesting.SO3
