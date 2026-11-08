module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-!
# Symplectic block decomposition

Every real symplectic matrix is a product of symmetric shears and an invertible
coordinate change. This standard background supplies the physical Gaussian
unitaries used in Section 6.

The symmetric-adjustment argument is adapted from the private lemma
`exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot` in Mathlib's
`LinearAlgebra/SymplecticGroup.lean` (Apache 2.0).
-/

namespace GaussianTesting

open Matrix

noncomputable section

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- A symmetric shear makes a Lagrangian coordinate block invertible. -/
theorem exists_symmetric_adjustment {R : Type*} [Field R]
    {A C : Matrix l l R} (hker : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) ↦ x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x → IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card l - C.rank) → R)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
      smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using hker _ heq1 heq2
    · exact f_unit hV
    · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, heq, hf,
      ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card l - C.rank)) (Fin C.rank ⊕
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def, isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
    · exact f_unit <| isUnit_nonsing_inv_iff.2 hU


variable {R : Type*} [Field R]

/-- A symplectic matrix admits a symmetric upper shear making its
upper-left block invertible. -/
theorem symplectic_exists_invertible_upper_block
    {A B C D : Matrix l l R}
    (h : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ X : Matrix l l R, X.IsSymm ∧ IsUnit (A + X * C) := by
  apply exists_symmetric_adjustment _ (SymplecticGroup.fromBlocks_mem_iff.mp h).1
  intro x hx hy
  have hu : IsUnit (fromBlocks A B C D) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (SymplecticGroup.symplectic_det h)
  change A *ᵥ x = 0 at hx
  change C *ᵥ x = 0 at hy
  have he : fromBlocks A B C D *ᵥ Sum.elim x 0 =
      fromBlocks A B C D *ᵥ Sum.elim 0 0 := by
    simp [fromBlocks_mulVec, hx, hy]
  exact (Sum.elim_eq_iff.mp (mulVec_injective_iff_isUnit.mpr hu he)).1

/-- With invertible upper-left block, a symplectic matrix has the usual
lower-shear, coordinate-change, upper-shear factorization. -/
theorem symplectic_block_decomposition
    {A B C D : Matrix l l R} [Invertible A]
    (h : fromBlocks A B C D ∈ symplecticGroup l R) :
    (C * A⁻¹).IsSymm ∧ (A⁻¹ * B).IsSymm ∧
      fromBlocks A B C D =
        fromBlocks 1 0 (C * A⁻¹) 1 *
          fromBlocks A 0 0 A⁻¹ᵀ * fromBlocks 1 (A⁻¹ * B) 0 1 := by
  have h₁ := (SymplecticGroup.fromBlocks_mem_iff.mp h).1
  have h₃ := (SymplecticGroup.fromBlocks_mem_iff.mp h).2.2
  have ht := SymplecticGroup.transpose_mem h
  rw [fromBlocks_transpose] at ht
  have h₂ := (SymplecticGroup.fromBlocks_mem_iff.mp ht).1
  simp only [transpose_transpose] at h₂
  let : Invertible Aᵀ := Matrix.invertibleTranspose A
  have hi : A⁻¹ * A = 1 := inv_mul_of_invertible A
  have hi' : A * A⁻¹ = 1 := mul_inv_of_invertible A
  have hit : A⁻¹ᵀ * Aᵀ = 1 := by rw [transpose_nonsing_inv, inv_mul_of_invertible]
  have hit' : Aᵀ * A⁻¹ᵀ = 1 := by rw [transpose_nonsing_inv, mul_inv_of_invertible]
  have hy : (C * A⁻¹).IsSymm := by
    change (C * A⁻¹)ᵀ = C * A⁻¹
    have hh := congrArg (fun M => A⁻¹ᵀ * M * A⁻¹) h₁
    simpa only [transpose_mul, mul_assoc, hi', mul_one, ← mul_assoc A⁻¹ᵀ Aᵀ, hit,
      one_mul] using hh.symm
  have hz : (A⁻¹ * B).IsSymm := by
    change (A⁻¹ * B)ᵀ = A⁻¹ * B
    have hh := congrArg (fun M => A⁻¹ * M * A⁻¹ᵀ) h₂
    simpa only [transpose_mul, mul_assoc, hit', mul_one, ← mul_assoc A⁻¹ A, hi,
      one_mul] using hh
  refine ⟨hy,hz,?_⟩
  have hd : D = A⁻¹ᵀ + C * A⁻¹ * B := by
    have hh := congrArg (fun M => A⁻¹ᵀ * M) h₃
    have hyt : A⁻¹ᵀ * Cᵀ = C * A⁻¹ := by simpa only [transpose_mul] using hy.eq
    simp only [mul_sub, ← mul_assoc, hit, one_mul, mul_one, hyt] at hh
    exact sub_eq_iff_eq_add.mp hh
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one,
    mul_assoc, hi, mul_inv_cancel_left_of_invertible, mul_one]
  congr 1
  simpa only [mul_assoc, add_comm] using hd

/-- Every symplectic matrix is a product of three symmetric shears and an
invertible coordinate change. The order of the blocks is position, momentum. -/
theorem symplectic_decomposition {S : Matrix (l ⊕ l) (l ⊕ l) R}
    (hS : S ∈ symplecticGroup l R) :
    ∃ X Y Z A : Matrix l l R,
      X.IsSymm ∧ Y.IsSymm ∧ Z.IsSymm ∧ IsUnit A ∧
      S = fromBlocks 1 X 0 1 * fromBlocks 1 0 Y 1 *
        fromBlocks A 0 0 A⁻¹ᵀ * fromBlocks 1 Z 0 1 := by
  let A := S.toBlocks₁₁
  let B := S.toBlocks₁₂
  let C := S.toBlocks₂₁
  let D := S.toBlocks₂₂
  have hs : fromBlocks A B C D ∈ symplecticGroup l R := by
    simpa only [A, B, C, D, fromBlocks_toBlocks] using hS
  obtain ⟨X,hX,hA⟩ := symplectic_exists_invertible_upper_block hs
  let L : Matrix (l ⊕ l) (l ⊕ l) R := fromBlocks 1 X 0 1
  have hL : L ∈ symplecticGroup l R := by
    apply SymplecticGroup.fromBlocks_mem_iff.mpr
    simp [hX.eq]
  have he : L * S = fromBlocks (A + X * C) (B + X * D) C D := by
    nth_rw 1 [← S.fromBlocks_toBlocks]
    simp only [L, fromBlocks_multiply, one_mul, zero_mul, zero_add]
    rfl
  have hh : fromBlocks (A + X * C) (B + X * D) C D ∈ symplecticGroup l R :=
    he ▸ (symplecticGroup l R).mul_mem hL hS
  let : Invertible (A + X * C) := hA.invertible
  obtain ⟨hy,hz,hdecomp⟩ := symplectic_block_decomposition hh
  refine ⟨-X, C * (A + X * C)⁻¹, (A + X * C)⁻¹ * (B + X * D),
    A + X * C, hX.neg, hy, hz, hA, ?_⟩
  have hl : fromBlocks 1 (-X) 0 1 * L = 1 := by
    simp [L, fromBlocks_multiply, ← fromBlocks_one]
  calc
    S = fromBlocks 1 (-X) 0 1 * (L * S) := by rw [← mul_assoc, hl, one_mul]
    _ = _ := by rw [he, hdecomp]; simp only [mul_assoc]

end
end GaussianTesting
