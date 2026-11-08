module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Coordinate-plane rotations

The real rotation convention matches the columns in the manuscript's
Majorana conjugation formula. These elementary matrix identities construct
the Gaussian implementers and also support the spherical Kac action.
-/

namespace GaussianTesting

noncomputable section

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real coordinate-plane rotation, in the column convention for Majorana conjugation. -/
def planeRotationMatrix (a b : ι) (p q : ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = a then (if j = a then p else if j = b then q else 0)
    else if i = b then (if j = a then -q else if j = b then p else 0)
    else if i = j then 1 else 0

private lemma sum_ite_two {a b : ι} (hab : a ≠ b) (f g : ι → ℝ) :
    (∑ x, if x = a then f x else if x = b then g x else 0) = f a + g b := by
  have h (x : ι) : (if x = a then f x else if x = b then g x else 0) =
      (if x = a then f x else 0) + (if x = b then g x else 0) := by
    by_cases ha : x = a
    · subst x; simp [hab]
    · simp [ha]
  simp_rw [h]
  simp [Finset.sum_add_distrib]

@[simp] theorem planeRotationMatrix_mulVec_a {a b : ι} (hab : a ≠ b) (p q : ℝ)
    (v : ι → ℝ) : (planeRotationMatrix a b p q).mulVec v a = p * v a + q * v b := by
  simpa [mulVec, dotProduct, planeRotationMatrix, ite_mul, hab, hab.symm] using
    sum_ite_two hab (fun x => p * v x) (fun x => q * v x)

@[simp] theorem planeRotationMatrix_mulVec_b {a b : ι} (hab : a ≠ b) (p q : ℝ)
    (v : ι → ℝ) : (planeRotationMatrix a b p q).mulVec v b = -q * v a + p * v b := by
  simpa [mulVec, dotProduct, planeRotationMatrix, ite_mul, hab, hab.symm] using
    sum_ite_two hab (fun x => -q * v x) (fun x => p * v x)

@[simp] theorem planeRotationMatrix_mulVec_other {a b c : ι}
    (hca : c ≠ a) (hcb : c ≠ b) (p q : ℝ) (v : ι → ℝ) :
    (planeRotationMatrix a b p q).mulVec v c = v c := by
  simp [mulVec, dotProduct, planeRotationMatrix, hca, hcb]

omit [Fintype ι] in
theorem planeRotationMatrix_transpose {a b : ι} (hab : a ≠ b) (p q : ℝ) :
    (planeRotationMatrix a b p q)ᵀ = planeRotationMatrix a b p (-q) := by
  ext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp_all [transpose_apply, planeRotationMatrix, eq_comm]

theorem planeRotationMatrix_mul_inv {a b : ι} (hab : a ≠ b) {p q : ℝ}
    (hpq : p ^ 2 + q ^ 2 = 1) :
    planeRotationMatrix a b p q * planeRotationMatrix a b p (-q) = 1 := by
  ext i j
  change (planeRotationMatrix a b p q).mulVec
    (fun k => planeRotationMatrix a b p (-q) k j) i = (1 : Matrix ι ι ℝ) i j
  by_cases hia : i = a
  · subst i
    rw [planeRotationMatrix_mulVec_a hab]
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
      simp_all [planeRotationMatrix, one_apply, eq_comm] <;> nlinarith [hpq]
  · by_cases hib : i = b
    · subst i
      rw [planeRotationMatrix_mulVec_b hab]
      by_cases hja : j = a <;> by_cases hjb : j = b <;>
        simp_all [planeRotationMatrix, one_apply, eq_comm] <;> nlinarith [hpq]
    · rw [planeRotationMatrix_mulVec_other hia hib]
      simp [planeRotationMatrix, hia, hib, one_apply]

theorem planeRotationMatrix_det {a b : ι} (hab : a ≠ b) (p q : ℝ) :
    (planeRotationMatrix a b p q).det = p ^ 2 + q ^ 2 := by
  let I : Matrix ι ι ℝ := 1
  have heq : planeRotationMatrix a b p q =
      (I.updateRow a (p • I a + q • I b)).updateRow b ((-q) • I a + p • I b) := by
    ext i j
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;>
      simp_all [planeRotationMatrix, updateRow_apply, I, one_apply, Pi.smul_apply, eq_comm]
  rw [heq, det_updateRow_add, det_updateRow_smul, det_updateRow_smul]
  rw [updateRow_comm _ hab, updateRow_comm _ hab]
  rw [det_updateRow_add, det_updateRow_smul, det_updateRow_smul,
    det_updateRow_add, det_updateRow_smul, det_updateRow_smul]
  have haa : ((I.updateRow b (I a)).updateRow a (I a)).det = 0 := by
    apply det_zero_of_row_eq hab
    simp [updateRow_ne hab.symm]
  have hbb : ((I.updateRow b (I b)).updateRow a (I b)).det = 0 := by
    apply det_zero_of_row_eq hab
    simp [updateRow_ne hab.symm]
  have hsame : ((I.updateRow b (I b)).updateRow a (I a)).det = 1 := by
    simp [I]
  have hswap : ((I.updateRow b (I a)).updateRow a (I b)).det = -1 := by
    have he : (I.updateRow b (I a)).updateRow a (I b) = I.submatrix (Equiv.swap a b) id := by
      ext i j
      by_cases hia : i = a <;> by_cases hib : i = b <;>
        simp_all [updateRow_apply, Equiv.swap_apply_def]
    rw [he, det_permute]
    simp [hab, I]
  rw [haa, hbb, hsame, hswap]
  ring

/-- The coordinate-plane matrix has determinant one and is orthogonal. -/
theorem planeRotationMatrix_mem {a b : ι} (hab : a ≠ b) {p q : ℝ}
    (hpq : p ^ 2 + q ^ 2 = 1) :
    planeRotationMatrix a b p q ∈ Matrix.specialOrthogonalGroup ι ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · rw [planeRotationMatrix_transpose hab]
    exact planeRotationMatrix_mul_inv hab hpq
  · exact (planeRotationMatrix_det hab p q).trans hpq

end
end GaussianTesting
