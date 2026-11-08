module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-!
# Compact operators commuting with a compact unitary representation

Averaging the rank-one operator onto an orbit gives a compact symmetric
operator commuting with the representation. It is nonzero for a nonzero
orbit vector. This is the analytic step in the compact-group decomposition
used to extend the Kac bound from finite-dimensional representations.
-/

namespace GaussianTesting.UnitaryRepresentation

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (π : G →* E ≃ₗᵢ[ℂ] E)
  (hπ : ∀ v : E, Continuous (fun g : G => π g v))
  (μ : Measure G) [IsProbabilityMeasure μ]

include hπ

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace E] in
/-- The norm-continuous rank-one orbit of a vector. -/
theorem continuous_rankOne_orbit (v : E) :
    Continuous (fun g : G => InnerProductSpace.rankOne ℂ (π g v) (π g v)) := by
  simp only [InnerProductSpace.rankOne_def]
  exact isBoundedBilinearMap_smulRight.continuous.comp
    (((innerSL ℂ).continuous.comp (hπ v)).prodMk (hπ v))

omit [IsTopologicalGroup G] [T2Space G] [CompleteSpace E] in
theorem integrable_rankOne_orbit (v : E) :
    Integrable (fun g : G => InnerProductSpace.rankOne ℂ (π g v) (π g v)) μ :=
  (continuous_rankOne_orbit π hπ v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Haar average of the rank-one orbit; the supplied Haar measure is normalized. -/
def compactAverage (v : E) : E →L[ℂ] E :=
  ∫ g, InnerProductSpace.rankOne ℂ (π g v) (π g v) ∂μ

omit [IsTopologicalGroup G] [T2Space G] [CompleteSpace E] in
theorem compactAverage_apply (v x : E) :
    compactAverage π μ v x =
      ∫ g, InnerProductSpace.rankOne ℂ (π g v) (π g v) x ∂μ :=
  ContinuousLinearMap.integral_apply (integrable_rankOne_orbit π hπ μ v) x

omit [IsTopologicalGroup G] [T2Space G] [CompleteSpace E] in
private theorem integrable_rankOne_orbit_apply (v x : E) :
    Integrable (fun g : G => InnerProductSpace.rankOne ℂ (π g v) (π g v) x) μ :=
  (ContinuousLinearMap.apply ℂ E x).integrable_comp
    (integrable_rankOne_orbit π hπ μ v)

omit [IsTopologicalGroup G] [T2Space G] in
/-- The averaged operator is compact: compact operators form a norm-closed
linear subspace, and each orbit operator has rank one. -/
theorem compactAverage_isCompactOperator (v : E) :
    IsCompactOperator (compactAverage π μ v) := by
  let K := compactOperator (RingHom.id ℂ) E E
  have hK : Convex ℝ (K : Set (E →L[ℂ] E)) := (K.restrictScalars ℝ).convex
  have hc : IsClosed (K : Set (E →L[ℂ] E)) := isClosed_setOfPred_isCompactOperator
  apply hK.integral_mem hc _ (integrable_rankOne_orbit π hπ μ v)
  apply Filter.Eventually.of_forall
  intro g
  change IsCompactOperator (InnerProductSpace.rankOne ℂ (π g v) (π g v))
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ (π g v))).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ (π g v))

omit [IsTopologicalGroup G] [T2Space G] in
/-- Haar averaging preserves symmetry. -/
theorem compactAverage_isSymmetric (v : E) :
    (compactAverage π μ v).IsSymmetric := by
  intro x y
  change inner ℂ (compactAverage π μ v x) y = inner ℂ x (compactAverage π μ v y)
  rw [compactAverage_apply π hπ μ, compactAverage_apply π hπ μ]
  calc
    inner ℂ (∫ g, InnerProductSpace.rankOne ℂ (π g v) (π g v) x ∂μ) y =
        (starRingEnd ℂ) (inner ℂ y (∫ g, InnerProductSpace.rankOne ℂ (π g v) (π g v) x ∂μ)) :=
      (inner_conj_symm _ _).symm
    _ = ∫ g, (starRingEnd ℂ) (inner ℂ y (InnerProductSpace.rankOne ℂ (π g v) (π g v) x)) ∂μ := by
      rw [← integral_inner (integrable_rankOne_orbit_apply π hπ μ v x), integral_conj]
    _ = ∫ g, inner ℂ x (InnerProductSpace.rankOne ℂ (π g v) (π g v) y) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        dsimp only
        rw [inner_conj_symm]
        exact InnerProductSpace.isSymmetric_rankOne_self (π g v) x y
    _ = _ := integral_inner (integrable_rankOne_orbit_apply π hπ μ v y) x

omit [T2Space G] in
/-- Left invariance of Haar measure makes the average commute with the group. -/
theorem compactAverage_commutes [Measure.IsMulLeftInvariant μ] (v : E) (g : G) (x : E) :
    compactAverage π μ v (π g x) = π g (compactAverage π μ v x) := by
  rw [compactAverage_apply π hπ μ, compactAverage_apply π hπ μ]
  calc
    _ = ∫ h, InnerProductSpace.rankOne ℂ (π (g * h) v) (π (g * h) v) (π g x) ∂μ :=
      (integral_mul_left_eq_self _ g).symm
    _ = ∫ h, π g (InnerProductSpace.rankOne ℂ (π h v) (π h v) x) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun h => by
        simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
          InnerProductSpace.rankOne_apply,
          LinearIsometryEquiv.inner_map_map, map_smul]
    _ = _ := (π g).toLinearIsometry.integral_comp_comm _

omit [IsTopologicalGroup G] [T2Space G] in
/-- A nonzero orbit vector gives a nonzero compact average. Positivity of
Haar measure on open sets detects its positive value at the identity. -/
theorem compactAverage_ne_zero [Measure.IsOpenPosMeasure μ] {v : E} (hv : v ≠ 0) :
    compactAverage π μ v ≠ 0 := by
  let f : G → ℝ := fun g => ‖inner ℂ (π g v) v‖ ^ 2
  have hf : Continuous f := ((hπ v).inner continuous_const).norm.pow 2
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hpos : 0 < ∫ g, f g ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero hf hfi (fun _ => sq_nonneg _) (x := 1) (by
      simp [f, hv])
  have he : (inner ℂ v (compactAverage π μ v v)).re = ∫ g, f g ∂μ := by
    change RCLike.re (inner ℂ v (compactAverage π μ v v)) = ∫ g, f g ∂μ
    rw [compactAverage_apply π hπ μ, ← integral_inner
      (integrable_rankOne_orbit_apply π hπ μ v v), ← integral_re]
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun g => by
        change (inner ℂ v (InnerProductSpace.rankOne ℂ (π g v) (π g v) v)).re =
          ‖inner ℂ (π g v) v‖ ^ 2
        rw [InnerProductSpace.inner_right_rankOne_apply, ← inner_conj_symm v (π g v)]
        rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    · exact (integrable_rankOne_orbit_apply π hπ μ v v).const_inner v
  intro hzero
  rw [hzero, zero_apply, inner_zero_right, Complex.zero_re] at he
  linarith

omit [T2Space G] in
/-- The analytic prerequisite for compact unitary decomposition. -/
theorem exists_compact_symmetric_commuting_ne_zero
    [Measure.IsMulLeftInvariant μ] [Measure.IsOpenPosMeasure μ]
    {v : E} (hv : v ≠ 0) :
    ∃ A : E →L[ℂ] E, IsCompactOperator A ∧ A.IsSymmetric ∧ A ≠ 0 ∧
      ∀ g x, A (π g x) = π g (A x) :=
  ⟨compactAverage π μ v, compactAverage_isCompactOperator π hπ μ v,
    compactAverage_isSymmetric π hπ μ v, compactAverage_ne_zero π hπ μ hv,
    compactAverage_commutes π hπ μ v⟩

end
end GaussianTesting.UnitaryRepresentation
