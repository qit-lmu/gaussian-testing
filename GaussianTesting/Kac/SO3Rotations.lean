module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# The coordinate-axis rotations in SO(3)

These are the three one-parameter subgroups used in the definition of the
Kac operator in Section 4 of the manuscript, with the usual right-handed
orientation of the coordinate axes.
-/

namespace GaussianTesting.SO3

open Matrix

noncomputable section

abbrev Group := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Rotation about the first coordinate axis. -/
def rotXMatrix (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos t, -Real.sin t; 0, Real.sin t, Real.cos t]

/-- Rotation about the second coordinate axis. -/
def rotYMatrix (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, 0, Real.sin t; 0, 1, 0; -Real.sin t, 0, Real.cos t]

/-- Rotation about the third coordinate axis. -/
def rotZMatrix (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]

private theorem rotX_mem (t : ℝ) : rotXMatrix t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotXMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]
  · simp [rotXMatrix, Matrix.det_fin_three]
    nlinarith [Real.sin_sq_add_cos_sq t]

private theorem rotY_mem (t : ℝ) : rotYMatrix t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotYMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]
  · simp [rotYMatrix, Matrix.det_fin_three]
    nlinarith [Real.sin_sq_add_cos_sq t]

private theorem rotZ_mem (t : ℝ) : rotZMatrix t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]
  · simp [rotZMatrix, Matrix.det_fin_three]
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- The first coordinate-axis subgroup. -/
def rotX (t : ℝ) : Group := ⟨rotXMatrix t, by exact rotX_mem t⟩
/-- The second coordinate-axis subgroup. -/
def rotY (t : ℝ) : Group := ⟨rotYMatrix t, by exact rotY_mem t⟩
/-- The third coordinate-axis subgroup. -/
def rotZ (t : ℝ) : Group := ⟨rotZMatrix t, by exact rotZ_mem t⟩

@[simp] theorem coe_rotX (t : ℝ) : (rotX t : Matrix (Fin 3) (Fin 3) ℝ) = rotXMatrix t := rfl
@[simp] theorem coe_rotY (t : ℝ) : (rotY t : Matrix (Fin 3) (Fin 3) ℝ) = rotYMatrix t := rfl
@[simp] theorem coe_rotZ (t : ℝ) : (rotZ t : Matrix (Fin 3) (Fin 3) ℝ) = rotZMatrix t := rfl

@[simp] theorem rotX_zero : rotX 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotXMatrix]

@[simp] theorem rotY_zero : rotY 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotYMatrix]

@[simp] theorem rotZ_zero : rotZ 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZMatrix]

theorem rotX_add (s t : ℝ) : rotX (s + t) = rotX s * rotX t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotXMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem rotY_add (s t : ℝ) : rotY (s + t) = rotY s * rotY t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotYMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem rotZ_add (s t : ℝ) : rotZ (s + t) = rotZ s * rotZ t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZMatrix, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem continuous_rotX : Continuous rotX := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotXMatrix, of_apply] <;> fun_prop

theorem continuous_rotY : Continuous rotY := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotYMatrix, of_apply] <;> fun_prop

theorem continuous_rotZ : Continuous rotZ := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotZMatrix, of_apply] <;> fun_prop

end
end GaussianTesting.SO3
