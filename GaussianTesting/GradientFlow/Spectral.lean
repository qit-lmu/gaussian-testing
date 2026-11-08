module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# The spectral gap and its quadratic polynomial

For a positive contraction the complex spectrum lies in the real interval
`[0,1]`. In the proof of Lemma 3.3, the continuous functional calculus tests
positivity of `(S − I)(S − αI)` by the sign of the corresponding scalar
polynomial on that interval.
-/

@[expose] public section

namespace GaussianTesting

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : H →L[ℂ] H}

/-- The real spectrum of a positive contraction is contained in `[0,1]`,
including on the zero Hilbert space. -/
theorem real_spectrum_subset_unitInterval (hS : 0 ≤ S) (hS_norm : ‖S‖ ≤ 1) :
    spectrum ℝ S ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  refine ⟨spectrum_nonneg_of_nonneg hS ht, ?_⟩
  calc
    t ≤ ‖t‖ := le_abs_self t
    _ ≤ ‖S‖ * ‖(1 : H →L[ℂ] H)‖ := spectrum.norm_le_norm_mul_of_mem ht
    _ ≤ 1 * 1 := mul_le_mul hS_norm ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

private theorem cfc_gap_polynomial (hS : IsSelfAdjoint S) (α : ℝ) :
    cfc (fun t : ℝ => (t - 1) * (t - α)) S =
      (S - 1) * (S - algebraMap ℝ (H →L[ℂ] H) α) := by
  rw [cfc_mul (fun t : ℝ => t - 1) (fun t : ℝ => t - α), cfc_sub (fun t : ℝ => t)
    (fun _ => 1), cfc_sub (fun t : ℝ => t) (fun _ => α), cfc_id' ℝ S hS,
    cfc_const_one ℝ S hS, cfc_const α S hS]

/-- The equivalence used in Lemma 3.3, for a positive contraction on any complex
Hilbert space, expressed in terms of its complex spectrum and the operator order. -/
theorem spectrum_gap_iff_polynomial_nonneg (hS : 0 ≤ S) (hS_norm : ‖S‖ ≤ 1) (α : ℝ) :
    (spectrum ℂ S ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1}) ↔
      0 ≤ (S - 1) * (S - algebraMap ℝ (H →L[ℂ] H) α) := by
  have hself := IsSelfAdjoint.of_nonneg hS
  rw [← cfc_gap_polynomial hself, cfc_nonneg_iff _ _ (by fun_prop) hself]
  have hspec : Complex.ofReal '' spectrum ℝ S = spectrum ℂ S :=
    hself.spectrumRestricts.algebraMap_image
  rw [← hspec]
  have hI := real_spectrum_subset_unitInterval hS hS_norm
  constructor
  · intro hgap t ht
    rcases hgap ⟨t, ht, rfl⟩ with ⟨u, hu, hu_eq⟩ | hone
    · have hut : u = t := Complex.ofReal_injective hu_eq
      subst u
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hI ht).2)
        (sub_nonpos.mpr hu.2)
    · have ht1 : t = 1 := by exact_mod_cast (show (t : ℂ) = 1 from hone)
      simp [ht1]
  · rintro hpoly _ ⟨t, ht, rfl⟩
    have ⟨ht0, ht1⟩ := hI ht
    rcases ht1.lt_or_eq with ht_lt | rfl
    · left
      exact ⟨t, ⟨ht0, le_of_not_gt fun h => (not_lt_of_ge (hpoly t ht))
        (mul_neg_of_neg_of_pos (sub_neg.mpr ht_lt) (sub_pos.mpr h))⟩, rfl⟩
    · right
      simp

open scoped InnerProductSpace

/-- The same spectral gap criterion evaluated on every vector, in the moment
form used in the proofs of Lemmas 3.3 and 6.6. -/
theorem spectrum_gap_iff_quadraticForm_nonneg (hS : 0 ≤ S) (hS_norm : ‖S‖ ≤ 1) (α : ℝ) :
    (spectrum ℂ S ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1}) ↔
      ∀ x : H, 0 ≤ (⟪x, S (S x)⟫_ℂ - (1 + (α : ℂ)) * ⟪x, S x⟫_ℂ
        + (α : ℂ) * ⟪x, x⟫_ℂ).re := by
  let Q := (S - 1) * (S - algebraMap ℝ (H →L[ℂ] H) α)
  have hself : IsSelfAdjoint Q := by
    change IsSelfAdjoint ((S - 1) * (S - _))
    rw [← cfc_gap_polynomial (IsSelfAdjoint.of_nonneg hS)]
    exact cfc_predicate _ _
  have hform (x : H) : ⟪x, Q x⟫_ℂ = ⟪x, S (S x)⟫_ℂ -
      (1 + (α : ℂ)) * ⟪x, S x⟫_ℂ + (α : ℂ) * ⟪x, x⟫_ℂ := by
    have hscalar : algebraMap ℝ (H →L[ℂ] H) α = (α : ℂ) • (1 : H →L[ℂ] H) := by
      rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul ℂ α (1 : H →L[ℂ] H)]
      rfl
    simp only [Q, hscalar, mul_apply_eq_comp, sub_apply, one_apply_eq_self, smul_apply,
      map_sub, map_smul, inner_sub_right, inner_smul_right]
    ring
  rw [spectrum_gap_iff_polynomial_nonneg hS hS_norm α]
  change 0 ≤ Q ↔ _
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  constructor
  · intro hQ x
    rw [← hform]
    exact hQ.re_inner_nonneg_right x
  · intro h
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself, fun x => ?_⟩
    change 0 ≤ (inner ℂ (Q x) x).re
    have hsymm : ⟪Q x, x⟫_ℂ = ⟪x, Q x⟫_ℂ :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself x x
    rw [hsymm, hform]
    exact h x

end GaussianTesting
