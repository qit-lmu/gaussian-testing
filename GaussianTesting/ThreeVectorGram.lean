/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

import Mathlib.Tactic

/-!
# The Gram matrix of three vectors with equal overlaps

The diagonal entries are one and the off-diagonal entries are `s`. Its
eigenvalue on the constant vector is `1 + 2*s`; on the two-dimensional
sum-zero space it is `1-s`. This is the matrix used in the manuscript's
three-axis calculations in Sections 4 and 6.
-/

@[expose] public section

namespace GaussianTesting

/-- The Gram matrix of three unit vectors with common real overlap `s`. -/
def threeVectorGram (s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun a b => if a = b then 1 else (s : ℂ)

/-- Characteristic polynomial, including the multiplicity-two eigenvalue. -/
theorem threeVectorGram_charpoly_eval (s : ℝ) (z : ℂ) :
    (threeVectorGram s).charpoly.eval z =
      (z - ((1 + 2 * s : ℝ) : ℂ)) * (z - ((1 - s : ℝ) : ℂ)) ^ 2 := by
  rw [Matrix.eval_charpoly]
  norm_num [threeVectorGram, Matrix.det_fin_three, Matrix.scalar, Matrix.diagonal]
  ring

/-- The exact two eigenvalues of the three-vector Gram matrix. -/
theorem threeVectorGram_spectrum (s : ℝ) :
    spectrum ℂ (threeVectorGram s) =
      {((1 + 2 * s : ℝ) : ℂ), ((1 - s : ℝ) : ℂ)} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  simp [Polynomial.IsRoot, threeVectorGram_charpoly_eval, sub_eq_zero]

/-- Coordinate form of the same spectral calculation, useful for transferring
nonzero eigenvalues between a Gram matrix and a sum of rank-one operators. -/
theorem threeVectorGram_eigenvalue_cases (s : ℝ) (x : Fin 3 → ℂ)
    (hx : x ≠ 0) (z : ℂ)
    (h : ∀ a, (1 - (s : ℂ)) * x a + s * (∑ b, x b) = z * x a) :
    z = ((1 + 2 * s : ℝ) : ℂ) ∨ z = ((1 - s : ℝ) : ℂ) := by
  have hsum : ((1 + 2 * s : ℝ) : ℂ) * (∑ a, x a) = z * (∑ a, x a) := by
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Fin.sum_univ_three] at *
    push_cast
    linear_combination h0 + h1 + h2
  by_cases hs : ∑ a, x a = 0
  · right
    obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
      by_contra! hh
      exact hx (funext hh)
    have hh := h a
    rw [hs, mul_zero, add_zero] at hh
    exact (mul_right_cancel₀ ha hh).symm.trans (by push_cast; rfl)
  · left
    exact (mul_right_cancel₀ hs hsum).symm

section ProjectionFamilies

variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype J] [DecidableEq J]

local notation "⟪" x ", " y "⟫_ℂ" => inner ℂ x y

/-- Inner coordinates of the average of three projection families. Distinct
labels `j` are orthogonal, so each coordinate triple is acted on by its Gram
matrix, divided by three. -/
theorem three_family_average_inner (e : Fin 3 → J → E) (s : J → ℝ)
    (hg : ∀ a b j k, ⟪e a j, e b k⟫_ℂ =
      if j = k then (if a = b then 1 else (s j : ℂ)) else 0)
    (S : E →ₗ[ℂ] E)
    (hS : ∀ v, S v = (1 / 3 : ℂ) • ∑ j, ∑ a, ⟪e a j, v⟫_ℂ • e a j)
    (v : E) (j : J) (a : Fin 3) :
    ⟪e a j, S v⟫_ℂ = (1 / 3 : ℂ) *
      ((1 - (s j : ℂ)) * ⟪e a j, v⟫_ℂ + s j * ∑ b, ⟪e b j, v⟫_ℂ) := by
  classical
  rw [hS]
  simp only [inner_smul_right, inner_sum, hg]
  fin_cases a <;> simp [Fin.sum_univ_three] <;> ring

/-- Every nonzero eigenvalue of the average comes from one of the two
eigenvalues of an actual coordinate Gram matrix. -/
theorem three_family_average_eigenvalue_cases (e : Fin 3 → J → E) (s : J → ℝ)
    (hg : ∀ a b j k, ⟪e a j, e b k⟫_ℂ =
      if j = k then (if a = b then 1 else (s j : ℂ)) else 0)
    (S : E →ₗ[ℂ] E)
    (hS : ∀ v, S v = (1 / 3 : ℂ) • ∑ j, ∑ a, ⟪e a j, v⟫_ℂ • e a j)
    (z : ℂ) (v : E) (hv : v ≠ 0) (he : S v = z • v) :
    z = 0 ∨ ∃ j, z = (((1 + 2 * s j) / 3 : ℝ) : ℂ) ∨
      z = (((1 - s j) / 3 : ℝ) : ℂ) := by
  classical
  by_cases hz : z = 0
  · exact Or.inl hz
  right
  obtain ⟨j, hj⟩ : ∃ j, (fun a => ⟪e a j, v⟫_ℂ) ≠ 0 := by
    by_contra! hzero
    have hSv : S v = 0 := by
      rw [hS]
      simp only [show ∀ j a, ⟪e a j, v⟫_ℂ = 0 from
        fun j a => congrFun (hzero j) a, zero_smul, Finset.sum_const_zero, smul_zero]
    exact hv ((smul_eq_zero.mp (he.symm.trans hSv)).resolve_left hz)
  refine ⟨j, ?_⟩
  have hc (a : Fin 3) :
      (1 - (s j : ℂ)) * ⟪e a j, v⟫_ℂ + s j * ∑ b, ⟪e b j, v⟫_ℂ =
        (3 * z) * ⟪e a j, v⟫_ℂ := by
    have h := three_family_average_inner e s hg S hS v j a
    rw [he, inner_smul_right] at h
    linear_combination -3 * h
  rcases threeVectorGram_eigenvalue_cases (s j) _ hj (3 * z) hc with h | h
  · left
    push_cast at h ⊢
    linear_combination h / 3
  · right
    push_cast at h ⊢
    linear_combination h / 3

/-- Action on one of the vectors in a projection family. -/
theorem three_family_average_apply_vector (e : Fin 3 → J → E) (s : J → ℝ)
    (hg : ∀ a b j k, ⟪e a j, e b k⟫_ℂ =
      if j = k then (if a = b then 1 else (s j : ℂ)) else 0)
    (S : E →ₗ[ℂ] E)
    (hS : ∀ v, S v = (1 / 3 : ℂ) • ∑ j, ∑ a, ⟪e a j, v⟫_ℂ • e a j)
    (j : J) (a : Fin 3) :
    S (e a j) = (1 / 3 : ℂ) •
      ((1 - (s j : ℂ)) • e a j + (s j : ℂ) • ∑ b, e b j) := by
  classical
  rw [hS]
  simp only [hg]
  simp only [ite_smul, zero_smul, one_smul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases a <;> simp [Fin.sum_univ_three] <;> module

/-- The nonzero spectrum of an average of three projection families is
exactly the union of the nonzero Gram eigenvalues, scaled by one third. -/
theorem three_family_average_mem_spectrum_iff [FiniteDimensional ℂ E]
    (e : Fin 3 → J → E) (s : J → ℝ)
    (hg : ∀ a b j k, ⟪e a j, e b k⟫_ℂ =
      if j = k then (if a = b then 1 else (s j : ℂ)) else 0)
    (S : E →ₗ[ℂ] E)
    (hS : ∀ v, S v = (1 / 3 : ℂ) • ∑ j, ∑ a, ⟪e a j, v⟫_ℂ • e a j)
    (z : ℂ) (hz : z ≠ 0) :
    z ∈ spectrum ℂ S ↔ ∃ j, z = (((1 + 2 * s j) / 3 : ℝ) : ℂ) ∨
      z = (((1 - s j) / 3 : ℝ) : ℂ) := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum h).exists_hasEigenvector
    exact (three_family_average_eigenvalue_cases e s hg S hS z v hv.2
      hv.apply_eq_smul).resolve_left hz
  · rintro ⟨j, rfl | rfl⟩
    · let v := ∑ a, e a j
      have hv : v ≠ 0 := by
        intro hv
        have h := congrArg (fun w => ⟪e 0 j, w⟫_ℂ) hv
        change ⟪e 0 j, ∑ a : Fin 3, e a j⟫_ℂ = ⟪e 0 j, 0⟫_ℂ at h
        rw [inner_sum] at h
        simp only [hg, inner_zero_right] at h
        norm_num [Fin.sum_univ_three] at h
        apply hz
        push_cast
        linear_combination h / 3
      have he : S v = (((1 + 2 * s j) / 3 : ℝ) : ℂ) • v := by
        simp only [v, map_sum, three_family_average_apply_vector e s hg S hS]
        simp only [Fin.sum_univ_three]
        push_cast
        module
      exact (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩).mem_spectrum
    · let v := e 0 j - e 1 j
      have hv : v ≠ 0 := by
        intro hv
        have h := congrArg (fun w => ⟪e 0 j, w⟫_ℂ) hv
        simp only [v, inner_sub_right, hg, inner_zero_right] at h
        norm_num at h
        apply hz
        push_cast
        linear_combination h / 3
      have he : S v = (((1 - s j) / 3 : ℝ) : ℂ) • v := by
        simp only [v, map_sub, three_family_average_apply_vector e s hg S hS]
        push_cast
        module
      exact (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩).mem_spectrum

end ProjectionFamilies

end GaussianTesting
