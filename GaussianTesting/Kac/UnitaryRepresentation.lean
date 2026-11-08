module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

@[expose] public section

/-!
# Invariant subspaces of unitary representations

These definitions support the compact-group decomposition used in Theorem 4.1.
The action is a homomorphism into linear isometric equivalences; continuity of
each orbit is supplied explicitly when needed, so no operator-norm continuity
of an infinite-dimensional representation is assumed.
-/

namespace GaussianTesting.UnitaryRepresentation

open scoped InnerProductSpace

noncomputable section

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A subspace is invariant if every group element preserves it. -/
def Invariant (π : G →* E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) : Prop :=
  ∀ g x, x ∈ U → π g x ∈ U

theorem Invariant.orthogonal {π : G →* E ≃ₗᵢ[ℂ] E} {U : Submodule ℂ E}
    (hU : Invariant π U) : Invariant π Uᗮ := by
  intro g w hw
  apply (U.mem_orthogonal _).mpr
  intro u hu
  have h := (U.mem_orthogonal w).mp hw (π g⁻¹ u) (hU g⁻¹ u hu)
  have he : π g (π g⁻¹ u) = u := by
    change (π g * π g⁻¹) u = u
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [← he, (π g).inner_map_map]
  exact h

/-- Restriction to an invariant subspace is again a unitary representation. -/
def restrict (π : G →* E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E)
    (hU : Invariant π U) : G →* U ≃ₗᵢ[ℂ] U where
  toFun g :=
    { toFun := fun x => ⟨π g x, hU g x x.property⟩
      invFun := fun x => ⟨π g⁻¹ x, hU g⁻¹ x x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (π g⁻¹ * π g) (x : E) = x
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        change (π g * π g⁻¹) (x : E) = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl
      map_add' := by intro x y; apply Subtype.ext; exact map_add (π g) (x : E) (y : E)
      map_smul' := by intro a x; apply Subtype.ext; exact map_smul (π g) a (x : E)
      norm_map' := fun x => (π g).norm_map x }
  map_one' := by
    ext x
    change π 1 (x : E) = x
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    ext x
    change π (g * h) (x : E) = π g (π h x)
    rw [map_mul]
    rfl

@[simp] theorem restrict_apply (π : G →* E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E)
    (hU : Invariant π U) (g : G) (x : U) :
    (restrict π U hU g x : E) = π g x := rfl

theorem continuous_restrict_orbit [TopologicalSpace G]
    (π : G →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ x, Continuous (fun g => π g x))
    (U : Submodule ℂ E) (hU : Invariant π U) (x : U) :
    Continuous (fun g => restrict π U hU g x) :=
  (hπ x).subtype_mk _

theorem Invariant.topologicalClosure {π : G →* E ≃ₗᵢ[ℂ] E}
    {U : Submodule ℂ E} (hU : Invariant π U) : Invariant π U.topologicalClosure := by
  intro g x hx
  have hm : Set.MapsTo (π g) (U : Set E) (U : Set E) := hU g
  exact hm.closure (π g).continuous hx

theorem Invariant.iSup {ι : Sort*} {π : G →* E ≃ₗᵢ[ℂ] E}
    {U : ι → Submodule ℂ E} (hU : ∀ i, Invariant π (U i)) :
    Invariant π (⨆ i, U i) := by
  intro g x hx
  have hle : (⨆ i, U i) ≤ (⨆ i, U i).comap (π g).toLinearMap := by
    apply iSup_le
    intro i y hy
    exact (le_iSup U i) (hU i g y hy)
  exact hle hx

/-- The fixed space for a subgroup; it is closed because each action map is continuous. -/
def fixedSubspace (π : G →* E ≃ₗᵢ[ℂ] E) (K : Subgroup G) : Submodule ℂ E where
  carrier := {x | ∀ g ∈ K, π g x = x}
  zero_mem' := by intro g _; exact map_zero _
  add_mem' := by intro x y hx hy g hg; simp only [map_add, hx g hg, hy g hg]
  smul_mem' := by intro a x hx g hg; simp only [map_smul, hx g hg]

theorem fixedSubspace_isClosed (π : G →* E ≃ₗᵢ[ℂ] E) (K : Subgroup G) :
    IsClosed (fixedSubspace π K : Set E) := by
  change IsClosed {x | ∀ g ∈ K, π g x = x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun g => isClosed_iInter (fun _ =>
    isClosed_eq (π g).continuous continuous_id))

instance fixedSubspace_complete [CompleteSpace E]
    (π : G →* E ≃ₗᵢ[ℂ] E) (K : Subgroup G) : CompleteSpace (fixedSubspace π K) :=
  (fixedSubspace_isClosed π K).completeSpace_coe

end
end GaussianTesting.UnitaryRepresentation
