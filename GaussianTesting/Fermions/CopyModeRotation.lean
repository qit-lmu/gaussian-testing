module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.SecondQuantization
public import GaussianTesting.Kac.SO3Rotations

@[expose] public section

/-!
# Rotating the three sets of fermionic modes

The one-particle action in Theorem 5.2 is `R ⊗ I_m`, indexed copy first.
-/

namespace GaussianTesting

noncomputable section

open Matrix
open scoped Kronecker

def copyModeMatrix (m : ℕ) (R : SO3.Group) : Matrix (Fin (3 * m)) (Fin (3 * m)) ℝ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (R.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ))

/-- The one-particle copy rotation `R ⊗ I_m`. -/
def fermionCopyModeRotation (m : ℕ) : SO3.Group →* FermionModeRotation (3 * m) where
  toFun R := ⟨copyModeMatrix m R, by
    refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
    · apply (Matrix.mem_orthogonalGroup_iff' _ _).mpr
      have hR := (Matrix.mem_orthogonalGroup_iff' _ _).mp R.property.1
      have ht : (R.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ))ᵀ =
          R.valᵀ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ) := by
        ext; simp [Matrix.one_apply, eq_comm]
      simp only [copyModeMatrix, Matrix.reindex_apply, Matrix.transpose_submatrix]
      rw [Matrix.submatrix_mul_equiv, ht, ← Matrix.mul_kronecker_mul,
        hR, one_mul, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
    · have hd : R.val.det = 1 := R.property.2
      rw [copyModeMatrix, Matrix.det_reindex_self, Matrix.det_kronecker,
        hd, Matrix.det_one]
      simp⟩
  map_one' := by
    apply Subtype.ext
    simp [copyModeMatrix]
  map_mul' R S := by
    apply Subtype.ext
    change copyModeMatrix m (R * S) = copyModeMatrix m R * copyModeMatrix m S
    simp only [copyModeMatrix, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    congr 1
    simpa using Matrix.mul_kronecker_mul R.val S.val
      (1 : Matrix (Fin m) (Fin m) ℝ) (1 : Matrix (Fin m) (Fin m) ℝ)

@[simp] theorem fermionCopyModeRotation_apply (m : ℕ) (R : SO3.Group)
    (a b : Fin 3) (k l : Fin m) :
    (fermionCopyModeRotation m R).val (finProdFinEquiv (a, k)) (finProdFinEquiv (b, l)) =
      if k = l then R.val a b else 0 := by
  simp [fermionCopyModeRotation, copyModeMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The copy-mode embedding is continuous in the matrix topology. -/
theorem continuous_fermionCopyModeRotation (m : ℕ) : Continuous (fermionCopyModeRotation m) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun R : SO3.Group =>
    R.val (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      (1 : Matrix (Fin m) (Fin m) ℝ) (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2)
  have hc : Continuous (fun R : SO3.Group =>
      R.val (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1) := by
    exact (continuous_apply (finProdFinEquiv.symm j).1).comp
      ((continuous_apply (finProdFinEquiv.symm i).1).comp continuous_subtype_val)
  exact hc.mul continuous_const

end
end GaussianTesting
