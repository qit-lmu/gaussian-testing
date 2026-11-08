module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.Defs
public import GaussianTesting.ThreeVectorGram
public import GaussianTesting.Kac.SpinOverlap
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

/-!
# Exact Gram eigenvalues for the three axis kernels

The nonzero eigenvalues of the mean of the three rank-one kernel projections
are the eigenvalues of the manuscript's Gram matrix divided by three. The
sum and difference vectors exhibit the two eigenvalues, whenever nonzero.
-/

namespace GaussianTesting.AngularMomentum

open scoped InnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- Unit spanning vectors for the three axis kernels, with the manuscript's
common real overlap. Choosing their phases does not change the projections. -/
structure AxisKernelVectors (J : AngularMomentum V) (s : ℝ) where
  vector : Fin 3 → V
  unit : ∀ a, ‖vector a‖ = 1
  kernel_x : LinearMap.ker J.Jx = ℂ ∙ vector 0
  kernel_y : LinearMap.ker J.Jy = ℂ ∙ vector 1
  kernel_z : LinearMap.ker J.Jz = ℂ ∙ vector 2
  gram : ∀ a b, ⟪vector a, vector b⟫_ℂ = if a = b then 1 else (s : ℂ)

namespace AxisKernelVectors

variable {J : AngularMomentum V} {s : ℝ} (D : AxisKernelVectors J s)

include D

/-- The Kac operator in the three unit kernel vectors. -/
theorem apply (f : V) : kacT J f =
    (3 : ℂ)⁻¹ • ∑ a, ⟪D.vector a, f⟫_ℂ • D.vector a := by
  simp only [kacT, LinearMap.smul_apply, ContinuousLinearMap.coe_coe, add_apply,
    D.kernel_x, D.kernel_y, D.kernel_z, Submodule.starProjection_singleton, D.unit,
    Fin.sum_univ_three]
  norm_num

private theorem inner_apply (a : Fin 3) (f : V) :
    ⟪D.vector a, kacT J f⟫_ℂ = (3 : ℂ)⁻¹ *
      ((1 - (s : ℂ)) * ⟪D.vector a, f⟫_ℂ + s * ∑ b, ⟪D.vector b, f⟫_ℂ) := by
  rw [D.apply]
  simp only [inner_smul_right, inner_sum, D.gram]
  congr 1
  fin_cases a <;> simp [Fin.sum_univ_three] <;> ring

/-- A nonzero Kac eigenvalue is one of the manuscript's two Gram eigenvalues. -/
theorem eigenvalue_cases {μ : ℂ} {f : V} (hμ : μ ≠ 0) (hf : f ≠ 0)
    (he : kacT J f = μ • f) :
    μ = (((1 + 2 * s) / 3 : ℝ) : ℂ) ∨ μ = (((1 - s) / 3 : ℝ) : ℂ) := by
  let x : Fin 3 → ℂ := fun a => ⟪D.vector a, f⟫_ℂ
  have hx : x ≠ 0 := by
    intro hz
    have hzero (a : Fin 3) : ⟪D.vector a, f⟫_ℂ = 0 := congrFun hz a
    rw [D.apply] at he
    simp only [hzero, zero_smul, Finset.sum_const_zero, smul_zero] at he
    exact hf ((smul_eq_zero.mp he.symm).resolve_left hμ)
  have hcoord (a : Fin 3) :
      (1 - (s : ℂ)) * x a + s * (∑ b, x b) = (3 * μ) * x a := by
    have h := D.inner_apply a f
    rw [he, inner_smul_right] at h
    dsimp [x]
    linear_combination -3 * h
  rcases threeVectorGram_eigenvalue_cases s x hx (3 * μ) hcoord with h | h
  · left
    push_cast at h ⊢
    linear_combination h / 3
  · right
    push_cast at h ⊢
    linear_combination h / 3

omit [FiniteDimensional ℂ V] in
private theorem inner_vector_sum (a : Fin 3) :
    ⟪D.vector a, ∑ b, D.vector b⟫_ℂ = ((1 + 2 * s : ℝ) : ℂ) := by
  simp only [inner_sum, D.gram]
  fin_cases a <;> simp [Fin.sum_univ_three] <;> ring

/-- The symmetric Gram eigenvector is the sum of the three kernel vectors. -/
theorem apply_sum : kacT J (∑ a, D.vector a) =
    (((1 + 2 * s) / 3 : ℝ) : ℂ) • ∑ a, D.vector a := by
  rw [D.apply]
  simp only [D.inner_vector_sum, ← Finset.smul_sum, smul_smul]
  congr 1
  push_cast
  ring

/-- Every difference of two distinct kernel vectors is a Gram eigenvector. -/
theorem apply_difference : kacT J (D.vector 0 - D.vector 1) =
    (((1 - s) / 3 : ℝ) : ℂ) • (D.vector 0 - D.vector 1) := by
  rw [D.apply]
  simp only [inner_sub_right, D.gram, Fin.sum_univ_three]
  norm_num
  module

/-- Exact transfer of the two nonzero Gram eigenvalues to the Kac operator. -/
theorem hasEigenvalue_iff {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (kacT J) μ ↔
      μ = (((1 + 2 * s) / 3 : ℝ) : ℂ) ∨ μ = (((1 - s) / 3 : ℝ) : ℂ) := by
  constructor
  · intro h
    obtain ⟨f, he, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector h
    exact D.eigenvalue_cases hμ hf (Module.End.mem_eigenspace_iff.mp he)
  · intro h
    rcases h with rfl | rfl
    · apply Module.End.hasEigenvalue_of_hasEigenvector (x := ∑ a, D.vector a)
      refine ⟨Module.End.mem_eigenspace_iff.mpr D.apply_sum, ?_⟩
      intro hz
      have h := D.inner_vector_sum 0
      rw [hz, inner_zero_right] at h
      apply hμ
      push_cast at h ⊢
      rw [← h, zero_div]
    · apply Module.End.hasEigenvalue_of_hasEigenvector (x := D.vector 0 - D.vector 1)
      refine ⟨Module.End.mem_eigenspace_iff.mpr D.apply_difference, ?_⟩
      intro hz
      have h := congrArg (fun v => ⟪D.vector 0, v⟫_ℂ) hz
      simp only [inner_sub_right, D.gram, Fin.isValue, ite_true, inner_zero_right] at h
      norm_num at h
      apply hμ
      push_cast
      rw [h, zero_div]

/-- The exact largest real eigenvalue is the maximum displayed in the manuscript. -/
theorem isGreatest_eigenvalue :
    IsGreatest {r : ℝ | Module.End.HasEigenvalue (kacT J) (r : ℂ)}
      (max ((1 + 2 * s) / 3) ((1 - s) / 3)) := by
  let m := max ((1 + 2 * s) / 3) ((1 - s) / 3)
  have hm : 0 < m := by
    have h₁ := le_max_left ((1 + 2 * s) / 3) ((1 - s) / 3)
    have h₂ := le_max_right ((1 + 2 * s) / 3) ((1 - s) / 3)
    dsimp [m]
    linarith
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · apply (D.hasEigenvalue_iff hmC).mpr
    rcases le_total ((1 + 2 * s) / 3) ((1 - s) / 3) with h | h
    · right
      dsimp [m]
      rw [max_eq_right h]
    · left
      dsimp [m]
      rw [max_eq_left h]
  · intro r hr
    by_cases hr0 : r = 0
    · subst r
      exact hm.le
    · have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
      rcases (D.hasEigenvalue_iff hrC).mp hr with h | h
      · have he : r = (1 + 2 * s) / 3 := Complex.ofReal_injective h
        rw [he]
        exact le_max_left _ _
      · have he : r = (1 - s) / 3 := Complex.ofReal_injective h
        rw [he]
        exact le_max_right _ _

/-- The exact Gram maximum controls the Kac quadratic form. -/
theorem quadratic_le : ∀ f : V, (⟪f, kacT J f⟫_ℂ).re ≤
    max ((1 + 2 * s) / 3) ((1 - s) / 3) * ‖f‖ ^ 2 := by
  have hT : (kacT J).IsSymmetric := by
    apply LinearMap.IsSymmetric.smul (by simp only [map_inv₀, map_ofNat])
    exact ((LinearMap.ker J.Jx).starProjection_isSymmetric.add
      (LinearMap.ker J.Jy).starProjection_isSymmetric).add
        (LinearMap.ker J.Jz).starProjection_isSymmetric
  let b := hT.eigenvectorBasis rfl
  let t := hT.eigenvalues rfl
  have ht (i : Fin (Module.finrank ℂ V)) :
      t i ≤ max ((1 + 2 * s) / 3) ((1 - s) / 3) :=
    D.isGreatest_eigenvalue.2 (hT.hasEigenvalue_eigenvalues rfl i)
  intro f
  have hnorm : (∑ i, Complex.normSq (b.repr f i)) = ‖f‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq, b.repr_apply_apply] using b.sum_sq_norm_inner_right f
  have hdiag : (⟪f, kacT J f⟫_ℂ).re =
      ∑ i, t i * Complex.normSq (b.repr f i) := by
    rw [← b.sum_inner_mul_inner f (kacT J f), Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hcoord : b.repr (kacT J f) i = (t i : ℂ) * b.repr f i :=
      hT.eigenvectorBasis_apply_self_apply rfl f i
    rw [← b.repr_apply_apply, hcoord]
    simp only [b.repr_apply_apply]
    change (⟪f, b i⟫_ℂ * ((t i : ℂ) * ⟪b i, f⟫_ℂ)).re =
      t i * Complex.normSq ⟪b i, f⟫_ℂ
    rw [mul_left_comm]
    have he : ⟪f, b i⟫_ℂ * ⟪b i, f⟫_ℂ = (Complex.normSq ⟪b i, f⟫_ℂ : ℂ) := by
      rw [← inner_conj_symm f (b i)]
      rw [mul_comm]
      exact Complex.mul_conj _
    rw [he]
    simp
  rw [hdiag, ← hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (ht i) (Complex.normSq_nonneg (b.repr f i)))

end AxisKernelVectors
end
end GaussianTesting.AngularMomentum
