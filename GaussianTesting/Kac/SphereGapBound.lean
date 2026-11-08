module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SphereFixedSpace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

/-!
# The spherical Kac bound away from constants

The compact-representation decomposition used in Theorem 4.1 also gives the
operator-norm bound on the orthogonal complement of constants. Each finite
invariant subspace of that complement has no invariant vector, hence no
eigenvalue one; its spectrum is therefore contained in `[0, 7/12]`. The
uniform norm bound extends to their dense span.
-/

namespace GaussianTesting.SO3

open UnitaryRepresentation
open scoped InnerProductSpace

noncomputable section

private theorem finite_kacAverage_norm_le_of_no_invariants
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] (π : Group →* E ≃ₗᵢ[ℂ] E)
    (hπ : ∀ v, Continuous (fun g => π g v))
    (hfixed : ∀ v, (∀ g, π g v = v) → v = 0) :
    ‖kacAverage π‖ ≤ 7 / 12 := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have he : kacAverage π = 0 := Subsingleton.elim _ _
    rw [he, norm_zero]
    norm_num
  | inr h =>
    have hp : 0 ≤ kacAverage π := groupKacAverage_nonneg π axisSubgroups
    have hn := CStarAlgebra.norm_mem_spectrum_of_nonneg (kacAverage π) hp
    have hnC : (‖kacAverage π‖ : ℂ) ∈ spectrum ℂ (kacAverage π) := by
      rw [← (IsSelfAdjoint.of_nonneg hp).spectrumRestricts.algebraMap_image]
      exact ⟨_, hn, rfl⟩
    rcases kacAverage_spectrum_subset π hπ hnC with ⟨r, hr, he⟩ | hone
    · have he' : r = ‖kacAverage π‖ := Complex.ofReal_injective he
      simpa only [he'] using hr.2
    · have hspec : (1 : ℂ) ∈ spectrum ℂ (kacAverage π) := by
        rwa [Set.mem_singleton_iff.mp hone] at hnC
      rw [ContinuousLinearMap.spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hspec
      obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspec
      have hvfix : kacAverage π v = v := by
        simpa only [Module.End.mem_eigenspace_iff, one_smul, ContinuousLinearMap.coe_coe] using hv
      exact (hvne (hfixed v ((kacAverage_eq_self_iff_invariant π v).mp hvfix))).elim

private theorem kacAverage_norm_le_of_no_invariants
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : Group →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ v, Continuous (fun g => π g v))
    (hfixed : ∀ v, (∀ g, π g v = v) → v = 0) :
    ‖kacAverage π‖ ≤ 7 / 12 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  have hd : Dense (finiteInvariantVectors π : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (finiteInvariantVectors_dense_haar π hπ)
  have hc : IsClosed {v : E | ‖kacAverage π v‖ ≤ (7 / 12 : ℝ) * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  suffices hh : (finiteInvariantVectors π : Set E) ⊆
      {v : E | ‖kacAverage π v‖ ≤ (7 / 12 : ℝ) * ‖v‖} from
    fun v => hc.closure_subset_iff.mpr hh (hd v)
  rintro v ⟨U, hU, hfd, hv⟩
  let : FiniteDimensional ℂ U := hfd
  have hno : ∀ u : U, (∀ g, restrict π U hU g u = u) → u = 0 := by
    intro u hu
    apply Subtype.ext
    exact hfixed u (fun g => congrArg Subtype.val (hu g))
  have hb := finite_kacAverage_norm_le_of_no_invariants (restrict π U hU)
    (continuous_restrict_orbit π hπ U hU) hno
  have he : kacAverage π v = (kacAverage (restrict π U hU) ⟨v, hv⟩ : E) :=
    groupKacAverage_restrict π axisSubgroups U hU ⟨v, hv⟩
  change ‖kacAverage π v‖ ≤ (7 / 12 : ℝ) * ‖v‖
  rw [he]
  exact (kacAverage (restrict π U hU)).le_of_opNorm_le hb ⟨v, hv⟩

/-- The mean-zero spherical L² subspace: the orthogonal complement of constants. -/
def sphereMeanZero : Submodule ℂ SphereSpace := sphereConstantsᗮ

/-- Mean-zero functions remain mean-zero under rotations. -/
theorem sphereMeanZero_invariant : Invariant sphereRepresentation sphereMeanZero := by
  apply Invariant.orthogonal
  intro g f hf
  obtain ⟨c, rfl⟩ := (mem_sphereConstants f).mp hf
  rw [sphereRepresentation_constant]
  exact (mem_sphereConstants _).mpr ⟨c, rfl⟩

instance sphereMeanZero_complete : CompleteSpace sphereMeanZero :=
  sphereConstants.isClosed_orthogonal.completeSpace_coe

/-- The rotation representation on mean-zero spherical functions. -/
def sphereMeanZeroRepresentation : Group →* sphereMeanZero ≃ₗᵢ[ℂ] sphereMeanZero :=
  restrict sphereRepresentation sphereMeanZero sphereMeanZero_invariant

/-- The Kac operator restricted to the orthogonal complement of constants. -/
def sphereMeanZeroKac : sphereMeanZero →L[ℂ] sphereMeanZero :=
  kacAverage sphereMeanZeroRepresentation

/-- The restricted Kac operator agrees with the spherical transition on its domain. -/
theorem sphereMeanZeroKac_coe (f : sphereMeanZero) :
    (sphereMeanZeroKac f : SphereSpace) = sphereKacTransition f := by
  rw [sphereKacTransition_eq_kacAverage]
  exact (groupKacAverage_restrict sphereRepresentation axisSubgroups sphereMeanZero
    sphereMeanZero_invariant f).symm

/-- The mean-zero representation has no nonzero invariant vectors. -/
theorem sphereMeanZero_invariant_eq_zero (f : sphereMeanZero)
    (hf : ∀ g, sphereMeanZeroRepresentation g f = f) : f = 0 := by
  have hconst : (f : SphereSpace) ∈ sphereConstants := by
    rw [mem_sphereConstants, ← sphereRepresentation_invariant_iff_constant]
    exact fun g => congrArg Subtype.val (hf g)
  have hz : (f : SphereSpace) = 0 :=
    Submodule.disjoint_def.mp sphereConstants.orthogonal_disjoint f hconst f.property
  exact Subtype.ext hz

/-- **Theorem 4.1, upper bound.** On the orthogonal complement of constants the
spherical Kac operator has norm at most `7/12`. -/
theorem sphereMeanZeroKac_norm_le : ‖sphereMeanZeroKac‖ ≤ 7 / 12 :=
  kacAverage_norm_le_of_no_invariants sphereMeanZeroRepresentation
    (continuous_restrict_orbit sphereRepresentation continuous_sphereRepresentation_orbit
      sphereMeanZero sphereMeanZero_invariant) sphereMeanZero_invariant_eq_zero

/-- The norm bound expressed in the ambient spherical L² space. -/
theorem sphereKacTransition_norm_le_on_orthogonal (f : SphereSpace)
    (hf : f ∈ sphereConstantsᗮ) : ‖sphereKacTransition f‖ ≤ (7 / 12 : ℝ) * ‖f‖ := by
  rw [← sphereMeanZeroKac_coe ⟨f, hf⟩]
  exact sphereMeanZeroKac.le_of_opNorm_le sphereMeanZeroKac_norm_le ⟨f, hf⟩

/-- The quadratic-form upper bound on mean-zero spherical functions. -/
theorem sphereKacTransition_quadratic_le_on_orthogonal (f : SphereSpace)
    (hf : f ∈ sphereConstantsᗮ) :
    (⟪f, sphereKacTransition f⟫_ℂ).re ≤ (7 / 12 : ℝ) * ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖f‖ * ‖sphereKacTransition f‖ := re_inner_le_norm (𝕜 := ℂ) f _
    _ ≤ ‖f‖ * ((7 / 12 : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (sphereKacTransition_norm_le_on_orthogonal f hf) (norm_nonneg f)
    _ = _ := by ring

/-- The spherical Kac transition is symmetric. -/
theorem sphereKacTransition_isSymmetric : sphereKacTransition.IsSymmetric := by
  rw [sphereKacTransition_eq_kacAverage]
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (groupKacAverage_nonneg sphereRepresentation axisSubgroups)).isSymmetric

/-- An eigenvector with eigenvalue different from one is orthogonal to constants. -/
theorem sphereKacTransition_eigenvector_mem_meanZero {f : SphereSpace} {μ : ℂ}
    (hμ : μ ≠ 1) (hf : sphereKacTransition f = μ • f) : f ∈ sphereMeanZero := by
  apply (sphereConstants.mem_orthogonal f).mpr
  intro c hc
  have hcfix : sphereKacTransition c = c :=
    (sphereKacTransition_eq_self_iff_constant c).mpr ((mem_sphereConstants c).mp hc)
  have he := sphereKacTransition_isSymmetric c f
  change ⟪sphereKacTransition c, f⟫_ℂ = ⟪c, sphereKacTransition f⟫_ℂ at he
  rw [hcfix, hf, inner_smul_right] at he
  by_contra hz
  exact hμ ((mul_eq_right₀ hz).mp he.symm)

end
end GaussianTesting.SO3
