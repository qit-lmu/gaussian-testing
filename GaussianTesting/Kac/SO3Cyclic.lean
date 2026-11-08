module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SO3Rotations

@[expose] public section

/-!
# Cyclic permutation of the three coordinate axes

Conjugation by the rotation that sends the first coordinate axis to the
second, the second to the third, and the third to the first transports the
three axis calculations into one another.
-/

namespace GaussianTesting.SO3

open Matrix

noncomputable section

def cycleMatrix : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private theorem cycleMatrix_mem : cycleMatrix ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [cycleMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [cycleMatrix, Matrix.det_fin_three]

/-- The rotation cyclically permuting the coordinate axes. -/
def axisCycle : Group := ⟨cycleMatrix, by exact cycleMatrix_mem⟩

private theorem axisCycle_mul_rotX (t : ℝ) : axisCycle * rotX t = rotY t * axisCycle := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisCycle, cycleMatrix, rotXMatrix, rotYMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem axisCycle_mul_rotY (t : ℝ) : axisCycle * rotY t = rotZ t * axisCycle := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisCycle, cycleMatrix, rotYMatrix, rotZMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem axisCycle_mul_rotZ (t : ℝ) : axisCycle * rotZ t = rotX t * axisCycle := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisCycle, cycleMatrix, rotZMatrix, rotXMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Cyclic relabeling of axes as a group automorphism of SO(3). -/
def cycleConj : Group ≃* Group := MulAut.conj axisCycle

@[simp] theorem cycleConj_rotX (t : ℝ) : cycleConj (rotX t) = rotY t := by
  change axisCycle * rotX t * axisCycle⁻¹ = rotY t
  rw [axisCycle_mul_rotX, mul_inv_cancel_right]

@[simp] theorem cycleConj_rotY (t : ℝ) : cycleConj (rotY t) = rotZ t := by
  change axisCycle * rotY t * axisCycle⁻¹ = rotZ t
  rw [axisCycle_mul_rotY, mul_inv_cancel_right]

@[simp] theorem cycleConj_rotZ (t : ℝ) : cycleConj (rotZ t) = rotX t := by
  change axisCycle * rotZ t * axisCycle⁻¹ = rotX t
  rw [axisCycle_mul_rotZ, mul_inv_cancel_right]

end
end GaussianTesting.SO3
