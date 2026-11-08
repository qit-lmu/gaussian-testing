module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereMeasure
public import GaussianTesting.Fermions.PlaneRotations

@[expose] public section

/-!
# Transitivity of rotations on the sphere

The constant functions are the rotation-invariant functions in the spherical
Kac realization in Section 4. The geometric ingredient is transitivity of
SO(3) on the unit sphere. Two elementary coordinate-plane rotations take any
unit vector to the first coordinate vector; composing these rotations proves
transitivity without making a measurable choice of a rotation.
-/

namespace GaussianTesting.SO3

noncomputable section

/-- The first coordinate unit vector, used as a basepoint for the transitive sphere action. -/
def spherePole : Sphere :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

private theorem plane_elimination_parameters (x y : ℝ) :
    ∃ p q : ℝ, p ^ 2 + q ^ 2 = 1 ∧ 0 ≤ p * x + q * y ∧ -q * x + p * y = 0 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · refine ⟨1, 0, by norm_num, ?_, ?_⟩ <;> simp <;>
      nlinarith [sq_nonneg x, sq_nonneg y]
  · have hs : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    let r := Real.sqrt (x ^ 2 + y ^ 2)
    have hr : 0 < r := Real.sqrt_pos.mpr hs
    have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hs.le
    refine ⟨x / r, y / r, ?_, ?_, ?_⟩
    · field_simp
      nlinarith
    · have : x / r * x + y / r * y = (x ^ 2 + y ^ 2) / r := by ring
      rw [this]
      positivity
    · ring

private theorem sphere_coordinate_squares (x : Sphere) :
    (x : SphereAmbient) 0 ^ 2 + (x : SphereAmbient) 1 ^ 2 +
      (x : SphereAmbient) 2 ^ 2 = 1 := by
  have hn : ‖(x : SphereAmbient)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hs := congrArg (fun t : ℝ => t ^ 2) hn
  simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, one_pow] using hs

private theorem exists_rotation_to_first_axis (x : Sphere) :
    ∃ g : Group, ∀ i : Fin 3,
      (sphereRotation g x : SphereAmbient) i = if i = 0 then 1 else 0 := by
  obtain ⟨p, q, hpq, -, hz⟩ :=
    plane_elimination_parameters ((x : SphereAmbient) 0) ((x : SphereAmbient) 1)
  let A : Group := ⟨planeRotationMatrix 0 1 p q,
    planeRotationMatrix_mem (by decide) hpq⟩
  let u := sphereRotation A x
  have hu1 : (u : SphereAmbient) 1 = 0 := by
    change (planeRotationMatrix (0 : Fin 3) 1 p q).mulVec
      (fun i => (x : SphereAmbient) i) 1 = 0
    rw [planeRotationMatrix_mulVec_b (by decide)]
    exact hz
  obtain ⟨r, s, hrs, hn, hz'⟩ :=
    plane_elimination_parameters ((u : SphereAmbient) 0) ((u : SphereAmbient) 2)
  let B : Group := ⟨planeRotationMatrix 0 2 r s,
    planeRotationMatrix_mem (by decide) hrs⟩
  let v := sphereRotation B u
  have hv0 : 0 ≤ (v : SphereAmbient) 0 := by
    change 0 ≤ (planeRotationMatrix (0 : Fin 3) 2 r s).mulVec
      (fun i => (u : SphereAmbient) i) 0
    rw [planeRotationMatrix_mulVec_a (by decide)]
    exact hn
  have hv1 : (v : SphereAmbient) 1 = 0 := by
    change (planeRotationMatrix (0 : Fin 3) 2 r s).mulVec
      (fun i => (u : SphereAmbient) i) 1 = 0
    rw [planeRotationMatrix_mulVec_other (by decide) (by decide)]
    exact hu1
  have hv2 : (v : SphereAmbient) 2 = 0 := by
    change (planeRotationMatrix (0 : Fin 3) 2 r s).mulVec
      (fun i => (u : SphereAmbient) i) 2 = 0
    rw [planeRotationMatrix_mulVec_b (by decide)]
    exact hz'
  have hv0' : (v : SphereAmbient) 0 = 1 := by
    have hsq := sphere_coordinate_squares v
    rw [hv1, hv2] at hsq
    nlinarith
  refine ⟨B * A, ?_⟩
  intro i
  rw [sphereRotation_mul]
  change (v : SphereAmbient) i = _
  fin_cases i
  · simpa using hv0'
  · simpa using hv1
  · simpa using hv2

/-- The natural SO(3) action on the unit sphere is transitive. -/
theorem sphereRotation_transitive (x y : Sphere) :
    ∃ g : Group, sphereRotation g x = y := by
  obtain ⟨a, ha⟩ := exists_rotation_to_first_axis x
  obtain ⟨b, hb⟩ := exists_rotation_to_first_axis y
  have he : sphereRotation a x = sphereRotation b y := by
    apply Subtype.ext
    ext i
    exact (ha i).trans (hb i).symm
  refine ⟨b⁻¹ * a, ?_⟩
  rw [sphereRotation_mul, he, ← sphereRotation_mul, inv_mul_cancel, sphereRotation_one]

end
end GaussianTesting.SO3
