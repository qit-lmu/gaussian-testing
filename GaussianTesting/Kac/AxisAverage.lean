module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SO3AxisSubgroups
public import GaussianTesting.Kac.SO3Topology
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

/-!
# Uniform circle averages and axis-invariant projections

For a strongly continuous unitary representation of SO(3), averaging its
vectors over one full turn about an axis is the orthogonal projection onto
the vectors fixed by that axis subgroup. These are Hilbert-space Bochner
integrals; no continuity in operator norm is assumed.
-/

namespace GaussianTesting.SO3

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Rotation through `θ` about the coordinate axis indexed by `a`. -/
def axisRotation (a : Fin 3) (θ : ℝ) : Group := ![rotX, rotY, rotZ] a θ

@[simp] theorem axisRotation_zero (a : Fin 3) : axisRotation a 0 = 1 := by
  fin_cases a <;> simp [axisRotation]

theorem axisRotation_add (a : Fin 3) (s t : ℝ) :
    axisRotation a (s + t) = axisRotation a s * axisRotation a t := by
  fin_cases a
  · exact rotX_add s t
  · exact rotY_add s t
  · exact rotZ_add s t

@[simp] theorem axisRotation_full_turn (a : Fin 3) : axisRotation a (2 * Real.pi) = 1 := by
  fin_cases a <;> apply Subtype.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [axisRotation, rotX, rotY, rotZ, rotXMatrix, rotYMatrix, rotZMatrix]

theorem axisRotation_periodic (a : Fin 3) : Function.Periodic (axisRotation a) (2 * Real.pi) := by
  intro t
  rw [axisRotation_add, axisRotation_full_turn, mul_one]

@[simp] theorem axisRotation_neg (a : Fin 3) (t : ℝ) :
    axisRotation a (-t) = (axisRotation a t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← axisRotation_add, neg_add_cancel, axisRotation_zero]

theorem continuous_axisRotation (a : Fin 3) : Continuous (axisRotation a) := by
  fin_cases a
  · exact continuous_rotX
  · exact continuous_rotY
  · exact continuous_rotZ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Fixed vectors for the axis subgroup are precisely vectors fixed at every angle. -/
theorem mem_fixedSubspace_axisRotation (π : Group →* E ≃ₗᵢ[ℂ] E) (a : Fin 3) (v : E) :
    v ∈ UnitaryRepresentation.fixedSubspace π (axisSubgroups a) ↔
      ∀ θ, π (axisRotation a θ) v = v := by
  fin_cases a
  · exact mem_fixedSubspace_axisX π v
  · exact mem_fixedSubspace_axisY π v
  · exact mem_fixedSubspace_axisZ π v

/-- The uniform circle average is the normalized Hilbert-space integral over one turn. -/
def axisCircleAverage (π : Group →* E ≃ₗᵢ[ℂ] E) (a : Fin 3) (v : E) : E :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in 0..2 * Real.pi, π (axisRotation a θ) v

variable (π : Group →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ v : E, Continuous (fun g => π g v))

omit [CompleteSpace E] in
include hπ in
/-- Each vector-valued orbit is integrable over a full circle. -/
theorem axisOrbit_intervalIntegrable (a : Fin 3) (v : E) :
    IntervalIntegrable (fun θ => π (axisRotation a θ) v) volume 0 (2 * Real.pi) :=
  ((hπ v).comp (continuous_axisRotation a)).intervalIntegrable _ _

omit [CompleteSpace E] in
private theorem axisOrbit_periodic (a : Fin 3) (v : E) :
    Function.Periodic (fun θ => π (axisRotation a θ) v) (2 * Real.pi) := by
  intro t
  change π (axisRotation a (t + 2 * Real.pi)) v = π (axisRotation a t) v
  rw [axisRotation_periodic a t]

/-- Uniform averaging is unchanged by any rotation about its axis. -/
theorem axisCircleAverage_mem_fixedSubspace (a : Fin 3) (v : E) :
    axisCircleAverage π a v ∈ UnitaryRepresentation.fixedSubspace π (axisSubgroups a) := by
  rw [mem_fixedSubspace_axisRotation]
  intro s
  let L : E →ₗᵢ[ℝ] E :=
    { toLinearMap := (π (axisRotation a s)).toLinearMap.restrictScalars ℝ
      norm_map' := (π (axisRotation a s)).norm_map }
  change L (((2 * Real.pi)⁻¹ : ℝ) • _) = _
  rw [map_smul, ← L.intervalIntegral_comp_comm]
  have he : (fun θ => L (π (axisRotation a θ) v)) =
      fun θ => π (axisRotation a (θ + s)) v := by
    funext θ
    change π (axisRotation a s) (π (axisRotation a θ) v) = _
    rw [add_comm θ s, axisRotation_add, map_mul]
    rfl
  rw [he, intervalIntegral.integral_comp_add_right (fun θ => π (axisRotation a θ) v) s]
  have hp := (axisOrbit_periodic π a v).intervalIntegral_add_eq s 0
  simpa [axisCircleAverage, zero_add, add_comm] using congrArg
    (fun z : E => ((2 * Real.pi)⁻¹ : ℝ) • z) hp

include hπ in
/-- Pairing with an axis-fixed vector is unchanged by averaging. -/
theorem inner_axisCircleAverage_of_fixed (a : Fin 3) (v w : E)
    (hw : w ∈ UnitaryRepresentation.fixedSubspace π (axisSubgroups a)) :
    ⟪w, axisCircleAverage π a v⟫_ℂ = ⟪w, v⟫_ℂ := by
  let L : E →L[ℝ] ℂ := ((innerSL ℂ) w).restrictScalars ℝ
  have hi : ∀ θ, L (π (axisRotation a θ) v) = ⟪w, v⟫_ℂ := by
    intro θ
    have hf := (mem_fixedSubspace_axisRotation π a w).mp hw θ
    change ⟪w, π (axisRotation a θ) v⟫_ℂ = ⟪w, v⟫_ℂ
    simpa only [hf] using (π (axisRotation a θ)).inner_map_map w v
  change L (((2 * Real.pi)⁻¹ : ℝ) • _) = _
  rw [map_smul, ← L.intervalIntegral_comp_comm (axisOrbit_intervalIntegrable π hπ a v)]
  simp only [hi, intervalIntegral.integral_const, sub_zero, smul_smul]
  rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_smul]

include hπ in
/-- Each axis-invariant orthogonal projection is the uniform circle average. -/
theorem axisCircleAverage_eq_fixedProjection (a : Fin 3) (v : E) :
    axisCircleAverage π a v =
      (UnitaryRepresentation.fixedSubspace π (axisSubgroups a)).starProjection v := by
  symm
  apply (UnitaryRepresentation.fixedSubspace π (axisSubgroups a)).eq_starProjection_of_mem_of_inner_eq_zero
    (axisCircleAverage_mem_fixedSubspace π a v)
  intro w hw
  rw [inner_sub_left]
  have hi := inner_axisCircleAverage_of_fixed π hπ a v w hw
  have hic := congrArg (starRingEnd ℂ) hi
  simpa only [inner_conj_symm, sub_eq_zero] using hic.symm

/-- The normalized integral, as a bounded complex-linear operator. -/
def axisCircleAverageCLM (a : Fin 3) : E →L[ℂ] E where
  toFun := axisCircleAverage π a
  map_add' v w := by
    simp only [axisCircleAverage_eq_fixedProjection π hπ, map_add]
  map_smul' z v := by
    simp only [axisCircleAverage_eq_fixedProjection π hπ, map_smul, RingHom.id_apply]
  cont := by
    have he : axisCircleAverage π a =
        (UnitaryRepresentation.fixedSubspace π (axisSubgroups a)).starProjection :=
      funext (axisCircleAverage_eq_fixedProjection π hπ a)
    rw [he]
    exact ContinuousLinearMap.continuous _

/-- Operator equality between uniform axis averaging and orthogonal projection. -/
theorem axisCircleAverageCLM_eq_fixedProjection (a : Fin 3) :
    axisCircleAverageCLM π hπ a =
      (UnitaryRepresentation.fixedSubspace π (axisSubgroups a)).starProjection := by
  ext v
  exact axisCircleAverage_eq_fixedProjection π hπ a v

end
end GaussianTesting.SO3
