module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Orientation in the real antisymmetric normal form

Changing the sign of one basis vector preserves the paired block form and
changes the sign of that block's coefficient. This converts an orthogonal
normal form into a special orthogonal one, without any hypothesis about
covariance matrices or Gaussian states.
-/

namespace GaussianTesting

open Matrix

noncomputable section

/-- The direct sum of the real antisymmetric blocks `!![0, c; -c, 0]`. -/
def skewBlockMatrix {m : ℕ} (c : Fin m → ℝ) :
    Matrix (Fin m × Bool) (Fin m × Bool) ℝ := fun i j =>
  if i.1 = j.1 then
    if i.2 = j.2 then 0 else if i.2 then -c i.1 else c i.1
  else 0

private theorem diagonal_conjugate_skewBlockMatrix {m : ℕ}
    (k₀ : Fin m) (t : ℝ) (c : Fin m → ℝ) :
    let D : Matrix (Fin m × Bool) (Fin m × Bool) ℝ :=
      diagonal (fun i => if i = (k₀, false) then t else 1)
    Dᵀ * skewBlockMatrix c * D =
      skewBlockMatrix (fun k => if k = k₀ then t * c k else c k) := by
  dsimp only
  rw [diagonal_transpose]
  ext ⟨k, b⟩ ⟨l, d⟩
  simp only [diagonal_mul, mul_diagonal]
  by_cases hkl : k = l
  · subst l
    by_cases hk : k = k₀ <;> cases b <;> cases d <;>
      simp [skewBlockMatrix, hk, mul_comm]
  · simp [skewBlockMatrix, hkl]

/-- An orthogonal paired normal form can be chosen with determinant one.
For nonzero dimension the only change is a possible sign change in one
column and in the corresponding block coefficient. -/
theorem exists_specialOrthogonal_skewBlockMatrix {m : ℕ}
    (A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ)
    (Q : Matrix.orthogonalGroup (Fin m × Bool) ℝ) (c : Fin m → ℝ)
    (hQ : Q.valᵀ * A * Q.val = skewBlockMatrix c) :
    ∃ (R : Matrix.specialOrthogonalGroup (Fin m × Bool) ℝ) (d : Fin m → ℝ),
      R.valᵀ * A * R.val = skewBlockMatrix d := by
  classical
  cases m with
  | zero =>
    refine ⟨1, c, ?_⟩
    ext i
    exact Fin.elim0 i.1
  | succ m =>
    let a : Fin (m + 1) × Bool := (0, false)
    let D : Matrix (Fin (m + 1) × Bool) (Fin (m + 1) × Bool) ℝ :=
      diagonal (fun i => if i = a then Q.val.det else 1)
    have hQtQ : Q.valᵀ * Q.val = 1 :=
      (Matrix.mem_orthogonalGroup_iff' _ _).mp Q.property
    have hdet : Q.val.det * Q.val.det = 1 := by
      simpa only [det_mul, det_transpose, det_one] using congrArg Matrix.det hQtQ
    have hDtD : Dᵀ * D = 1 := by
      dsimp [D]
      rw [diagonal_transpose, diagonal_mul_diagonal]
      ext i j
      by_cases hi : i = a <;> simp [diagonal_apply, hi, hdet, one_apply]
    have hDdet : D.det = Q.val.det := by
      simp [D, det_diagonal]
    let R : Matrix.specialOrthogonalGroup (Fin (m + 1) × Bool) ℝ :=
      ⟨Q.val * D, (Matrix.mem_specialOrthogonalGroup_iff).mpr ⟨
        (Matrix.mem_orthogonalGroup_iff' _ _).mpr (by
          rw [transpose_mul, mul_assoc, ← mul_assoc Q.valᵀ, hQtQ,
            one_mul, hDtD]), by rw [det_mul, hDdet, hdet]⟩⟩
    refine ⟨R, (fun k => if k = 0 then Q.val.det * c k else c k), ?_⟩
    change (Q.val * D)ᵀ * A * (Q.val * D) = _
    rw [transpose_mul]
    have hreassoc : (Dᵀ * Q.valᵀ) * A * (Q.val * D) =
        Dᵀ * (Q.valᵀ * A * Q.val) * D := by simp only [mul_assoc]
    rw [hreassoc, hQ]
    exact diagonal_conjugate_skewBlockMatrix 0 Q.val.det c

end
end GaussianTesting
