module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import GaussianTesting.Fermions.SkewNormalFormOrientation

@[expose] public section

/-!
# Real antisymmetric block normal form

The orthogonal block normal form used in the covariance-matrix proof of
manuscript Lemma 5.1. This is a statement about arbitrary real antisymmetric
operators, independent of the purity or Gaussianity of a state.
-/

namespace GaussianTesting

noncomputable section

open scoped InnerProductSpace
open Module Submodule Matrix

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private lemma skew_inner_self (T : E →ₗ[ℝ] E)
    (hT : ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ) (x : E) :
    ⟪x, T x⟫_ℝ = 0 := by
  have h := hT x x
  rw [real_inner_comm] at h
  linarith

/-- A nonzero real antisymmetric operator has an invariant orthonormal two-plane. -/
private lemma skew_exists_plane (T : E →ₗ[ℝ] E)
    (hT : ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ) (hne : T ≠ 0) :
    ∃ (v : Bool → E) (c : ℝ), Orthonormal ℝ v ∧
      T (v false) = -c • v true ∧ T (v true) = c • v false := by
  let S : E →ₗ[ℝ] E := -(T * T)
  have hS : S.IsSymmetric := by
    intro x y
    simp only [S, LinearMap.neg_apply, Module.End.mul_apply, inner_neg_left,
      inner_neg_right]
    rw [hT (T x) y, hT x (T y)]
    ring
  let b := hS.eigenvectorBasis rfl
  obtain ⟨i, hi⟩ : ∃ i, T (b i) ≠ 0 := by
    by_contra! h
    apply hne
    exact b.toBasis.ext (fun i => by simpa using h i)
  let x := b i
  let d : ℝ := ‖T x‖
  have hd : 0 < d := norm_pos_iff.mpr hi
  have hx : ‖x‖ = 1 := b.orthonormal.1 i
  have heig : -(T (T x)) = hS.eigenvalues rfl i • x := by
    exact hS.apply_eigenvectorBasis rfl i
  have heval : hS.eigenvalues rfl i = d ^ 2 := by
    have h := congrArg (fun z => ⟪x, z⟫_ℝ) heig
    rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, hx] at h
    have h' := hT x (T x)
    rw [real_inner_self_eq_norm_sq] at h'
    dsimp [d]
    nlinarith
  have hsq : T (T x) = -(d ^ 2) • x := by
    rw [heval] at heig
    simpa using congrArg Neg.neg heig
  let y := d⁻¹ • T x
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, d, ne_of_gt hd]
  have hxy : ⟪x, y⟫_ℝ = 0 := by
    simp [y, inner_smul_right, skew_inner_self T hT x]
  have hyx : ⟪y, x⟫_ℝ = 0 := by rwa [real_inner_comm]
  refine ⟨fun b => if b then y else x, -d, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro a b
    cases a <;> cases b <;>
      simp [hx, hy, hxy, hyx]
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_neg]
    simp [y, smul_smul, ne_of_gt hd]
  · simp only [↓reduceIte, Bool.false_eq_true]
    rw [show y = d⁻¹ • T x from rfl, map_smul, hsq, smul_smul]
    congr 1
    field_simp

private lemma skew_exists_orthonormal_pairs (m : ℕ) (T : E →ₗ[ℝ] E)
    (hT : ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ)
    (hdim : finrank ℝ E = 2 * m) :
    ∃ (v : Fin m × Bool → E) (c : Fin m → ℝ), Orthonormal ℝ v ∧
      ∀ k, T (v (k, false)) = -c k • v (k, true) ∧
        T (v (k, true)) = c k • v (k, false) := by
  classical
  induction m generalizing E with
  | zero =>
    exact ⟨fun i => Fin.elim0 i.1, fun i => Fin.elim0 i,
      by rw [orthonormal_iff_ite]; exact fun i => Fin.elim0 i.1,
      fun i => Fin.elim0 i⟩
  | succ m ih =>
    by_cases hzero : T = 0
    · let b : OrthonormalBasis (Fin (m + 1) × Bool) ℝ E :=
        (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq (by
          simpa [mul_comm] using hdim))
      exact ⟨b, fun _ => 0, b.orthonormal, by simp [hzero]⟩
    obtain ⟨v, c, hv, hv0, hv1⟩ := skew_exists_plane T hT hzero
    let W := Submodule.span ℝ (Set.range v)
    have hvW (a : Bool) : v a ∈ W := Submodule.subset_span (Set.mem_range_self a)
    have hW : ∀ x ∈ W, T x ∈ W := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        cases a
        · rw [hv0]; exact W.smul_mem _ (hvW true)
        · rw [hv1]; exact W.smul_mem _ (hvW false)
      | zero => simp
      | add x y hx hy hTx hTy => simpa only [map_add] using W.add_mem hTx hTy
      | smul a x hx hTx => simpa only [map_smul] using W.smul_mem a hTx
    have hK : ∀ x ∈ Wᗮ, T x ∈ Wᗮ := by
      intro x hx
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hxy := Submodule.inner_right_of_mem_orthogonal (hW y hy) hx
      have hs := hT y x
      linarith
    have hdimW : finrank ℝ W = 2 := by
      simpa [W] using finrank_span_eq_card hv.linearIndependent
    have hdimK : finrank ℝ Wᗮ = 2 * m := by
      have h := W.finrank_add_finrank_orthogonal
      omega
    obtain ⟨w, d, hw, hwd⟩ := ih (T.restrict hK) (fun x y => hT x y) hdimK
    let u : Fin (m + 1) × Bool → E := fun i =>
      Fin.cases (v i.2) (fun k => (w (k, i.2) : E)) i.1
    have hcross (a : Bool) (j : Fin m × Bool) : ⟪v a, (w j : E)⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hvW a) (w j).property
    have hcross' (a : Bool) (j : Fin m × Bool) : ⟪(w j : E), v a⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact hcross a j
    have hon : Orthonormal ℝ u := by
      rw [orthonormal_iff_ite] at hv hw ⊢
      rintro ⟨i, a⟩ ⟨j, b⟩
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simpa [u] using hv a b
        | succ j => simp [u, hcross, Ne.symm (Fin.succ_ne_zero j)]
      | succ i =>
        induction j using Fin.cases with
        | zero => simp [u, hcross']
        | succ j => simpa [u] using hw (i, a) (j, b)
    refine ⟨u, Fin.cases c d, hon, ?_⟩
    intro k
    induction k using Fin.cases with
    | zero => simpa [u] using And.intro hv0 hv1
    | succ k =>
      simpa [u] using And.intro
        (congrArg Subtype.val (hwd k).1) (congrArg Subtype.val (hwd k).2)

end InnerProductSpace

private lemma skew_toEuclideanLin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, A j i = -A i j) :
    ∀ x y, ⟪Matrix.toEuclideanLin A x, y⟫_ℝ =
      -⟪x, Matrix.toEuclideanLin A y⟫_ℝ := by
  have ht : Aᵀ = -A := by ext i j; exact hA i j
  intro x y
  simp only [PiLp.inner_apply, Real.inner_apply, Matrix.toLpLin_apply]
  change (A *ᵥ WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y =
    -(WithLp.ofLp x ⬝ᵥ (A *ᵥ WithLp.ofLp y))
  rw [dotProduct_comm, ← dotProduct_transpose_mulVec, ht]
  simp only [neg_mulVec, dotProduct_neg]

/-- Every real antisymmetric matrix in even dimension has orthogonal paired block form. -/
theorem exists_orthogonal_skewBlockMatrix {m : ℕ}
    (A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ)
    (hA : ∀ i j, A j i = -A i j) :
    ∃ (Q : Matrix.orthogonalGroup (Fin m × Bool) ℝ) (c : Fin m → ℝ),
      Q.valᵀ * A * Q.val = skewBlockMatrix c := by
  classical
  let T := Matrix.toEuclideanLin A
  obtain ⟨v, c, hv, hvc⟩ := skew_exists_orthonormal_pairs m T
    (skew_toEuclideanLin A hA) (by simp [mul_comm])
  let Q : Matrix (Fin m × Bool) (Fin m × Bool) ℝ := fun i j => v j i
  have hQ : Qᵀ * Q = 1 := by
    ext i j
    change (∑ k, v i k * v j k) = if i = j then 1 else 0
    have h := (orthonormal_iff_ite.mp hv) i j
    simpa only [PiLp.inner_apply, Real.inner_apply] using h
  refine ⟨⟨Q, (Matrix.mem_orthogonalGroup_iff' _ _).mpr hQ⟩, c, ?_⟩
  have hentry (i j) : (Qᵀ * A * Q) i j = ⟪v i, T (v j)⟫_ℝ := by
    rw [Matrix.mul_assoc]
    simp only [Q, Matrix.mul_apply, PiLp.inner_apply, Real.inner_apply,
      T, Matrix.toLpLin_apply, mulVec, dotProduct]
    rfl
  change Qᵀ * A * Q = _
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [hentry]
  cases b
  · rw [(hvc j).1, inner_smul_right, orthonormal_iff_ite.mp hv]
    by_cases hij : i = j <;> cases a <;> simp [skewBlockMatrix, hij]
  · rw [(hvc j).2, inner_smul_right, orthonormal_iff_ite.mp hv]
    by_cases hij : i = j <;> cases a <;> simp [skewBlockMatrix, hij]

/-- The real antisymmetric normal form with a special orthogonal change of basis,
as used in manuscript Lemma 5.1. Block coefficients may have either sign. -/
theorem exists_specialOrthogonal_skewNormalForm {m : ℕ}
    (A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ)
    (hA : ∀ i j, A j i = -A i j) :
    ∃ (R : Matrix.specialOrthogonalGroup (Fin m × Bool) ℝ) (c : Fin m → ℝ),
      R.valᵀ * A * R.val = skewBlockMatrix c := by
  obtain ⟨Q, c, hQ⟩ := exists_orthogonal_skewBlockMatrix A hA
  exact exists_specialOrthogonal_skewBlockMatrix A Q c hQ

end
end GaussianTesting
