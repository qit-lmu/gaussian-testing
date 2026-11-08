module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberInner
public import GaussianTesting.Bosons.PolynomialGaussianDensity
public import GaussianTesting.Bosons.SchrodingerVacuum
public import GaussianTesting.Bosons.Fock

@[expose] public section

/-! # The oscillator number basis in the Schrödinger representation

Normalized creation powers of the Gaussian vacuum form an orthonormal Hilbert
basis of actual Lebesgue `L²`. This identifies the occupation-number Fock space
with the manuscript's wavefunction space without assuming completeness.
-/

namespace GaussianTesting

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {σ : Type*} [Fintype σ]

private theorem polynomialGaussian_one_norm_sq :
    ‖polynomialGaussian (1 : MvPolynomial σ ℂ)‖ ^ 2 =
      Real.pi ^ ((Fintype.card σ : ℝ) / 2) := by
  let f := polynomialGaussian (1 : MvPolynomial σ ℂ)
  change ‖f‖ ^ 2 = _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  calc
    (∫ x, RCLike.re (inner ℂ (f x) (f x))) =
        ∫ x : EuclideanSpace ℝ σ, Real.exp (-‖x‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [polynomialGaussian_coeFn (1 : MvPolynomial σ ℂ)] with x hx
      change RCLike.re (inner ℂ (polynomialGaussian (1 : MvPolynomial σ ℂ) x)
        (polynomialGaussian (1 : MvPolynomial σ ℂ) x)) = _
      rw [hx]
      simp only [polynomialGaussianFun, map_one, one_mul,
        inner_self_eq_norm_sq_to_K, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), ← RCLike.ofReal_pow, RCLike.ofReal_re]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by
      simpa only [neg_one_mul, div_one, finrank_euclideanSpace] using
        (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ σ)
          (by norm_num : (0 : ℝ) < 1))

/-- The normalized ordered creation powers of the Gaussian vacuum. -/
def schrodingerNumberVector (n : σ → ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ σ)) :=
  ((Real.pi ^ (-(Fintype.card σ : ℝ) / 4) /
    Real.sqrt (∏ j, ((n j).factorial : ℝ)) : ℝ) : ℂ) •
      polynomialGaussian (fockNumberPolynomialRaw n)

private theorem numberNormalization_ne_zero (n : σ → ℕ) :
    ((Real.pi ^ (-(Fintype.card σ : ℝ) / 4) /
      Real.sqrt (∏ j, ((n j).factorial : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.sqrt_pos.mpr (Finset.prod_pos fun j _ =>
      Nat.cast_pos.mpr (Nat.factorial_pos (n j)))))

private theorem numberNormalization_sq (n : σ → ℕ) :
    (Real.pi ^ (-(Fintype.card σ : ℝ) / 4) /
      Real.sqrt (∏ j, ((n j).factorial : ℝ))) ^ 2 *
        (∏ j, ((n j).factorial : ℝ)) * Real.pi ^ ((Fintype.card σ : ℝ) / 2) = 1 := by
  have hp : (0 : ℝ) < ∏ j, ((n j).factorial : ℝ) :=
    Finset.prod_pos fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos (n j))
  rw [div_pow, Real.sq_sqrt hp.le, div_mul_cancel₀ _ hp.ne']
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul Real.pi_pos.le,
    ← Real.rpow_add Real.pi_pos]
  rw [show -(Fintype.card σ : ℝ) / 4 * (2 : ℕ) + (Fintype.card σ : ℝ) / 2 = 0 by
    push_cast; ring, Real.rpow_zero]

/-- Each normalized number vector is a unit vector. -/
theorem inner_schrodingerNumberVector_self (n : σ → ℕ) :
    inner ℂ (schrodingerNumberVector n) (schrodingerNumberVector n) = 1 := by
  have hbase : inner ℂ (polynomialGaussian (1 : MvPolynomial σ ℂ))
      (polynomialGaussian (1 : MvPolynomial σ ℂ)) =
        ((Real.pi ^ ((Fintype.card σ : ℝ) / 2) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, polynomialGaussian_one_norm_sq]
    rfl
  rw [schrodingerNumberVector, inner_smul_left, inner_smul_right,
    inner_fockNumberPolynomialRaw_self, hbase]
  simp only [Complex.conj_ofReal]
  have h := numberNormalization_sq n
  push_cast at h ⊢
  convert congrArg Complex.ofReal h using 1
  push_cast
  ring

/-- Number vectors with distinct occupation vectors are orthogonal. -/
theorem inner_schrodingerNumberVector_eq_zero (n k : σ → ℕ) (h : n ≠ k) :
    inner ℂ (schrodingerNumberVector n) (schrodingerNumberVector k) = 0 := by
  simp only [schrodingerNumberVector, inner_smul_left, inner_smul_right,
    inner_fockNumberPolynomialRaw_eq_zero n k h, mul_zero]

/-- The manuscript's normalized creation powers are orthonormal in actual `L²`. -/
theorem orthonormal_schrodingerNumberVector :
    Orthonormal ℂ (schrodingerNumberVector (σ := σ)) := by
  classical
  rw [orthonormal_iff_ite]
  intro n k
  split_ifs with h
  · subst k; exact inner_schrodingerNumberVector_self n
  · exact inner_schrodingerNumberVector_eq_zero n k h

/-- Number vectors span the full polynomial Gaussian subspace. -/
theorem span_schrodingerNumberVector :
    Submodule.span ℂ (Set.range (schrodingerNumberVector (σ := σ))) =
      LinearMap.range (polynomialGaussianLinear (ι := σ)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨n,rfl⟩
    apply Submodule.smul_mem
    exact ⟨fockNumberPolynomialRaw n, rfl⟩
  · let S := Submodule.span ℂ (Set.range (schrodingerNumberVector (σ := σ)))
    have htop : ⊤ ≤ S.comap (polynomialGaussianLinear (ι := σ)) := by
      rw [← span_fockNumberPolynomialRaw_eq_top]
      apply Submodule.span_le.mpr
      rintro p ⟨n,rfl⟩
      change polynomialGaussian (fockNumberPolynomialRaw n) ∈ S
      have h : schrodingerNumberVector n ∈ S := Submodule.subset_span ⟨n,rfl⟩
      have h' := S.smul_mem
        (((Real.pi ^ (-(Fintype.card σ : ℝ) / 4) /
          Real.sqrt (∏ j, ((n j).factorial : ℝ)) : ℝ) : ℂ)⁻¹) h
      simpa only [schrodingerNumberVector, smul_smul,
        inv_mul_cancel₀ (numberNormalization_ne_zero n), one_smul] using h'
    rintro f ⟨p,rfl⟩
    exact htop (Submodule.mem_top : p ∈ (⊤ : Submodule ℂ _))

/-- Completeness of the number vectors follows from density of polynomial Gaussians. -/
theorem dense_span_schrodingerNumberVector :
    (Submodule.span ℂ (Set.range (schrodingerNumberVector (σ := σ)))).topologicalClosure = ⊤ := by
  rw [span_schrodingerNumberVector, polynomialGaussian_range_topologicalClosure]

/-- The manuscript's oscillator number basis, proved complete in the position representation. -/
def schrodingerNumberBasis : HilbertBasis (σ → ℕ) ℂ
    (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ σ))) :=
  HilbertBasis.mk orthonormal_schrodingerNumberVector
    (le_of_eq dense_span_schrodingerNumberVector.symm)

@[simp] theorem schrodingerNumberBasis_apply (n : σ → ℕ) :
    schrodingerNumberBasis n = schrodingerNumberVector n := by
  exact congrFun (HilbertBasis.coe_mk _ _) n

/-- Unitary identification of occupation amplitudes with actual wavefunctions. -/
def schrodingerFockEquiv : lp (fun _ : σ → ℕ => ℂ) 2 ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ σ)) :=
  schrodingerNumberBasis.repr.symm

/-- The unit occupation vector maps to the corresponding normalized creation power. -/
@[simp] theorem schrodingerFockEquiv_single [DecidableEq (σ → ℕ)] (n : σ → ℕ) :
    schrodingerFockEquiv (lp.single 2 n 1) = schrodingerNumberVector n := by
  exact (schrodingerNumberBasis.repr_symm_single n).trans (schrodingerNumberBasis_apply n)

/-- The manuscript's `m`-mode Fock and Schrödinger spaces are unitarily equivalent. -/
def fockSchrodingerEquiv (m : ℕ) : FockB m ≃ₗᵢ[ℂ] WaveSpace m :=
  schrodingerFockEquiv

@[simp] theorem fockSchrodingerEquiv_single (m : ℕ) (n : Fin m → ℕ) :
    fockSchrodingerEquiv m (lp.single 2 n 1) = schrodingerNumberVector n := by
  classical
  exact schrodingerFockEquiv_single n

@[simp] theorem fockNumberPolynomialRaw_zero :
    fockNumberPolynomialRaw (fun _ : σ => 0) = 1 := by
  simp only [fockNumberPolynomialRaw, Function.iterate_zero, id_eq]
  have h (l : List (Fin (Fintype.card σ))) :
      l.foldr (fun _ p => p) (1 : MvPolynomial σ ℂ) = 1 := by
    induction l <;> simp_all
  exact h _

/-- The zero-occupation number vector is the normalized Gaussian vacuum. -/
@[simp] theorem schrodingerNumberVector_zero (m : ℕ) :
    schrodingerNumberVector (fun _ : Fin m => 0) = waveVacuum m := by
  simp [schrodingerNumberVector, waveVacuum]

@[simp] theorem fockSchrodingerEquiv_vacuum (m : ℕ) :
    fockSchrodingerEquiv m (lp.single 2 (fun _ : Fin m => 0) 1) = waveVacuum m := by
  rw [fockSchrodingerEquiv_single, schrodingerNumberVector_zero]

/-- For two copies these normalized vectors are precisely the finite-core
number polynomials already used to define the physical generator. -/
theorem schrodingerNumberVector_eq_fockNumberPolynomial (m : ℕ)
    (n : (Fin 2 × Fin m) → ℕ) :
    schrodingerNumberVector n = polynomialGaussian (fockNumberPolynomial m n) := by
  simp only [schrodingerNumberVector, fockNumberPolynomial, polynomialGaussian_smul,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]

end
end GaussianTesting
