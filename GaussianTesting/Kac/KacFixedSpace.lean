module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.AxisAverage
public import GaussianTesting.Kac.GeneralRepresentation
public import GaussianTesting.Fermions.SpecialOrthogonalGeneration
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# Fixed vectors of the Kac operator

A vector fixed by the average of three orthogonal projections is fixed by
all three projections. For SO(3), the coordinate-axis rotations generate
the full group, so the Kac-fixed vectors are precisely the invariant vectors.
-/

namespace GaussianTesting

noncomputable section

namespace UnitaryRepresentation

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The fixed space of the Kac average is the intersection of its three
subgroup-fixed spaces. -/
theorem groupKacAverage_eq_self_iff (π : G →* E ≃ₗᵢ[ℂ] E)
    (K : Fin 3 → Subgroup G) (v : E) :
    groupKacAverage π K v = v ↔ ∀ a, v ∈ fixedSubspace π (K a) := by
  constructor
  · intro hv
    let P := fun a => (fixedSubspace π (K a)).starProjection
    have hsum : P 0 v + P 1 v + P 2 v = (3 : ℂ) • v := by
      have h := congrArg (fun x : E => (3 : ℂ) • x) hv
      simpa only [groupKacAverage, smul_apply,
        add_apply, smul_smul, mul_inv_cancel₀ (by norm_num : (3 : ℂ) ≠ 0),
        one_smul] using h
    have hnorm : 3 * ‖v‖ ≤ ‖P 0 v‖ + ‖P 1 v‖ + ‖P 2 v‖ := by
      have h := norm_add_le (P 0 v + P 1 v) (P 2 v)
      rw [hsum, norm_smul] at h
      norm_num only [Complex.norm_ofNat] at h
      linarith [norm_add_le (P 0 v) (P 1 v)]
    have hp (a : Fin 3) : ‖P a v‖ ≤ ‖v‖ :=
      (fixedSubspace π (K a)).norm_starProjection_apply_le v
    intro a
    apply (Submodule.mem_iff_norm_starProjection _ v).mpr
    fin_cases a
    · change ‖P 0 v‖ = ‖v‖
      linarith [hp 0, hp 1, hp 2]
    · change ‖P 1 v‖ = ‖v‖
      linarith [hp 0, hp 1, hp 2]
    · change ‖P 2 v‖ = ‖v‖
      linarith [hp 0, hp 1, hp 2]
  · intro hv
    simp only [groupKacAverage, smul_apply,
      add_apply,
      (fixedSubspace π (K 0)).starProjection_eq_self_iff.mpr (hv 0),
      (fixedSubspace π (K 1)).starProjection_eq_self_iff.mpr (hv 1),
      (fixedSubspace π (K 2)).starProjection_eq_self_iff.mpr (hv 2)]
    module

end UnitaryRepresentation

namespace SO3

private theorem exists_cos_sin_of_sq_add_sq_eq_one {p q : ℝ} (hpq : p ^ 2 + q ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = p ∧ Real.sin θ = q := by
  let z : ℂ := ⟨p, q⟩
  have hz : ‖z‖ = 1 := by
    simp only [z, Complex.norm_def, Complex.normSq_mk, ← pow_two, hpq, Real.sqrt_one]
  refine ⟨z.arg, ?_, ?_⟩
  · simpa only [hz, one_mul] using Complex.norm_mul_cos_arg z
  · simpa only [hz, one_mul] using Complex.norm_mul_sin_arg z

/-- In three dimensions every coordinate-plane rotation is a rotation about
one of the three coordinate axes. -/
theorem coordinatePlaneRotation_eq_axisRotation (a b : Fin 3) (p q : ℝ)
    (hab : a ≠ b) (hpq : p ^ 2 + q ^ 2 = 1) :
    ∃ c θ, coordinatePlaneRotation a b p q hab hpq = axisRotation c θ := by
  obtain ⟨θ, hc, hs⟩ := exists_cos_sin_of_sq_add_sq_eq_one hpq
  fin_cases a <;> fin_cases b <;> try exact (hab rfl).elim
  · refine ⟨2, -θ, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, planeRotationMatrix, axisRotation, rotZ, rotZMatrix, hc, hs]
  · refine ⟨1, θ, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, planeRotationMatrix, axisRotation, rotY, rotYMatrix, hc, hs]
  · refine ⟨2, θ, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, planeRotationMatrix, axisRotation, rotZ, rotZMatrix, hc, hs]
  · refine ⟨0, -θ, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, planeRotationMatrix, axisRotation, rotX, rotXMatrix, hc, hs]
  · refine ⟨1, -θ, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, planeRotationMatrix, axisRotation, rotY, rotYMatrix, hc, hs]
  · refine ⟨0, θ, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, planeRotationMatrix, axisRotation, rotX, rotXMatrix, hc, hs]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Fixing every coordinate-axis rotation is equivalent to fixing every rotation. -/
theorem invariant_iff_axisRotation (π : Group →* E ≃ₗᵢ[ℂ] E) (v : E) :
    (∀ g, π g v = v) ↔ ∀ a θ, π (axisRotation a θ) v = v := by
  constructor
  · intro h a θ
    exact h _
  · intro h g
    induction g using specialOrthogonal_induction with
    | h1 => simp
    | hmul A B hA hB =>
      rw [map_mul]
      change π A (π B v) = v
      rw [hB, hA]
    | hinv A hA =>
      have he : π A⁻¹ (π A v) = v := by
        change (π A⁻¹ * π A) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      rwa [hA] at he
    | hplane a b p q hab hpq =>
      obtain ⟨c, θ, he⟩ := coordinatePlaneRotation_eq_axisRotation a b p q hab hpq
      rw [he]
      exact h c θ

variable [CompleteSpace E]

/-- A Kac-fixed vector is exactly a vector fixed by every axis rotation. -/
theorem kacAverage_eq_self_iff_axisRotation (π : Group →* E ≃ₗᵢ[ℂ] E) (v : E) :
    kacAverage π v = v ↔ ∀ a θ, π (axisRotation a θ) v = v := by
  rw [kacAverage, UnitaryRepresentation.groupKacAverage_eq_self_iff]
  simp only [mem_fixedSubspace_axisRotation]

/-- The fixed space of the SO(3) Kac average is the full invariant space. -/
theorem kacAverage_eq_self_iff_invariant (π : Group →* E ≃ₗᵢ[ℂ] E) (v : E) :
    kacAverage π v = v ↔ ∀ g, π g v = v := by
  rw [kacAverage_eq_self_iff_axisRotation, invariant_iff_axisRotation]

end SO3
end
end GaussianTesting
