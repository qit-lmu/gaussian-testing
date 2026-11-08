module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.SO3Rotations
public import GaussianTesting.Kac.UnitaryRepresentation

@[expose] public section

/-!
# The three rotation subgroups in the Kac average

Each subgroup is the image of the corresponding one-parameter axis
rotation. Fixed vectors therefore agree with vectors fixed at every angle.
-/

namespace GaussianTesting.SO3

noncomputable section

/-- The homomorphism parametrizing rotations around the first coordinate axis. -/
def rotXHom : Multiplicative ℝ →* Group where
  toFun t := rotX t.toAdd
  map_one' := rotX_zero
  map_mul' s t := rotX_add s.toAdd t.toAdd

/-- The homomorphism parametrizing rotations around the second coordinate axis. -/
def rotYHom : Multiplicative ℝ →* Group where
  toFun t := rotY t.toAdd
  map_one' := rotY_zero
  map_mul' s t := rotY_add s.toAdd t.toAdd

/-- The homomorphism parametrizing rotations around the third coordinate axis. -/
def rotZHom : Multiplicative ℝ →* Group where
  toFun t := rotZ t.toAdd
  map_one' := rotZ_zero
  map_mul' s t := rotZ_add s.toAdd t.toAdd

/-- The coordinate-axis rotation subgroups appearing in Eq. (4.1). -/
def axisSubgroups : Fin 3 → Subgroup Group := ![rotXHom.range, rotYHom.range, rotZHom.range]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

@[simp] theorem mem_fixedSubspace_axisX (π : Group →* E ≃ₗᵢ[ℂ] E) (v : E) :
    v ∈ UnitaryRepresentation.fixedSubspace π (axisSubgroups 0) ↔
      ∀ t, π (rotX t) v = v := by
  constructor
  · intro hv t
    exact hv (rotX t) ⟨Multiplicative.ofAdd t, rfl⟩
  · rintro hv _ ⟨t, rfl⟩
    exact hv t.toAdd

@[simp] theorem mem_fixedSubspace_axisY (π : Group →* E ≃ₗᵢ[ℂ] E) (v : E) :
    v ∈ UnitaryRepresentation.fixedSubspace π (axisSubgroups 1) ↔
      ∀ t, π (rotY t) v = v := by
  constructor
  · intro hv t
    exact hv (rotY t) ⟨Multiplicative.ofAdd t, rfl⟩
  · rintro hv _ ⟨t, rfl⟩
    exact hv t.toAdd

@[simp] theorem mem_fixedSubspace_axisZ (π : Group →* E ≃ₗᵢ[ℂ] E) (v : E) :
    v ∈ UnitaryRepresentation.fixedSubspace π (axisSubgroups 2) ↔
      ∀ t, π (rotZ t) v = v := by
  constructor
  · intro hv t
    exact hv (rotZ t) ⟨Multiplicative.ofAdd t, rfl⟩
  · rintro hv _ ⟨t, rfl⟩
    exact hv t.toAdd

end
end GaussianTesting.SO3
