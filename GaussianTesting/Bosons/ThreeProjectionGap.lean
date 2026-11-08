/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GaussianTesting.ThreeVectorGram
public import Mathlib.Analysis.InnerProductSpace.Spectrum

import Mathlib.Tactic

/-!
# The three-projection calculation in Lemma 6.6

Three orthonormal families with cross-family overlaps `s j` give orthogonal
three-vector sectors. Their nonzero eigenvalues are exactly `(1+2*s j)/3`
and `(1-s j)/3`, by the Gram calculation in `ThreeVectorGram`.

On a finite particle-number block, diagonalizing the self-adjoint average
therefore proves `(S-I)(S-I/2) ≥ 0` whenever `s j=1` or
`-1/2 ≤ s j ≤ 1/4`. This polynomial consequence of the exact sector spectra
is used only to assemble the infinitely many orthogonal particle-number
blocks in `Coherent.lean`.
-/

public section

namespace GaussianTesting

open Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {J : Type*} [Fintype J] [DecidableEq J]

local notation "⟪" x ", " y "⟫_ℂ" => inner ℂ x y

/-- The polynomial gap on a finite block, derived from the exact
three-vector Gram eigenvalues in the manuscript. -/
theorem three_projection_gap_of_gram (e : Fin 3 → J → E) (s : J → ℝ)
    (hGram : ∀ a b : Fin 3, ∀ j j' : J,
      ⟪e a j, e b j'⟫_ℂ =
        if j = j' then (if a = b then 1 else (s j : ℂ)) else 0)
    (hs : ∀ j, s j = 1 ∨ (-(1/2) ≤ s j ∧ s j ≤ 1/4))
    (Pr3 : Fin 3 → E →ₗ[ℂ] E)
    (hPr : ∀ a v, Pr3 a v = ∑ j, ⟪e a j, v⟫_ℂ • e a j)
    (S : E →ₗ[ℂ] E) (hS : S = (3 : ℂ)⁻¹ • (Pr3 0 + Pr3 1 + Pr3 2))
    (v : E) :
    0 ≤ (⟪v, ((S - LinearMap.id) ∘ₗ
        (S - (((1 / 2 : ℝ) : ℂ) • LinearMap.id))) v⟫_ℂ).re := by
  classical
  have happly (u : E) : S u =
      (1 / 3 : ℂ) • ∑ j, ∑ a, ⟪e a j, u⟫_ℂ • e a j := by
    simp [hS, hPr, Fin.sum_univ_three, Finset.sum_add_distrib, smul_add]
  have hPr_sym (a : Fin 3) : (Pr3 a).IsSymmetric := by
    intro u w
    simp [hPr, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      inner_conj_symm, mul_comm]
  have hT : S.IsSymmetric := by
    rw [hS]
    exact ((hPr_sym 0).add (hPr_sym 1) |>.add (hPr_sym 2)).smul
      (by simp only [map_inv₀, map_ofNat])
  let b := hT.eigenvectorBasis rfl
  let t := hT.eigenvalues rfl
  have ht (i : Fin (Module.finrank ℂ E)) :
      t i = 1 ∨ t i ≤ (1 / 2 : ℝ) := by
    have he := hT.apply_eigenvectorBasis rfl i
    change S (b i) = (t i : ℂ) • b i at he
    rcases three_family_average_eigenvalue_cases e s hGram S happly (t i : ℂ)
        (b i) (b.orthonormal.ne_zero i) he with hz | ⟨j, hj | hj⟩
    · right
      have : t i = 0 := by exact_mod_cast hz
      linarith
    · have hj' : t i = (1 + 2 * s j) / 3 := Complex.ofReal_injective hj
      rcases hs j with hs | ⟨hlo, hhi⟩
      · left
        rw [hs] at hj'
        linarith
      · right
        linarith
    · right
      have hj' : t i = (1 - s j) / 3 := Complex.ofReal_injective hj
      rcases hs j with hs | ⟨hlo, hhi⟩
      · rw [hs] at hj'
        linarith
      · linarith
  let Q : Module.End ℂ E := (S - LinearMap.id) ∘ₗ
    (S - (((1 / 2 : ℝ) : ℂ) • LinearMap.id))
  have hdiag (u : E) (i : Fin (Module.finrank ℂ E)) :
      b.repr (Q u) i =
        (((t i - 1) * (t i - 1 / 2) : ℝ) : ℂ) * b.repr u i := by
    have hcoord (w : E) : b.repr (S w) i = (t i : ℂ) * b.repr w i :=
      hT.eigenvectorBasis_apply_self_apply rfl w i
    simp only [Q, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
      hcoord, smul_eq_mul]
    push_cast
    ring
  change 0 ≤ (⟪v, Q v⟫_ℂ).re
  rw [← b.sum_inner_mul_inner v (Q v), Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [← b.repr_apply_apply, hdiag]
  have hprod : 0 ≤ (t i - 1) * (t i - 1 / 2) := by
    rcases ht i with h | h
    · simp [h]
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  rw [b.repr_apply_apply]
  have he : ⟪v, b i⟫_ℂ *
      ((((t i - 1) * (t i - 1 / 2) : ℝ) : ℂ) * ⟪b i, v⟫_ℂ) =
      (((t i - 1) * (t i - 1 / 2) : ℝ) : ℂ) *
        (⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ) := by ring
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg hprod
  rw [← Complex.mul_re, ← RCLike.re_eq_complex_re, inner_mul_symm_re_eq_norm]
  positivity

end GaussianTesting
