module

public import GaussianTesting.GradientFlow.ProjectiveSpace

/-! # Centered affine coordinates for the tangent space of a ray

At a unit representative `x`, subtracting `x` identifies the affine hyperplane
of chart representatives with the complex orthogonal complement of `x`.
In these coordinates the origin represents the ray of `x`.
-/

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Horizontal tangent vectors, in the coordinates of a representative `x`. -/
abbrev RayTangent (x : H) : Type _ := ↥(innerSL ℂ x).ker

/-- The Fubini–Study pairing in horizontal coordinates is the real part of the
complex inner product. -/
noncomputable instance rayTangentRealInner (x : H) : InnerProductSpace ℝ (RayTangent x) :=
  InnerProductSpace.rclikeToReal ℂ (RayTangent x)

instance rayTangentCompleteSpace [CompleteSpace H] (x : H) : CompleteSpace (RayTangent x) :=
  (innerSL ℂ x).isClosed_ker.completeSpace_coe

theorem inner_add_rayTangent (x : H) (hx : ‖x‖ = 1) (v : RayTangent x) :
    ⟪x, x + (v : H)⟫_ℂ = 1 := by
  have hv : ⟪x, (v : H)⟫_ℂ = 0 := v.property
  simp [inner_add_right, inner_self_eq_norm_sq_to_K, hx, hv]

theorem add_rayTangent_ne_zero (x : H) (hx : ‖x‖ = 1) (v : RayTangent x) :
    x + (v : H) ≠ 0 := by
  intro h
  simpa [h] using inner_add_rayTangent x hx v

theorem rayChart_sub_mem (x : H) (hx : ‖x‖ = 1) (w : {w : H // ⟪x, w⟫_ℂ = 1}) :
    (w : H) - x ∈ (innerSL ℂ x).ker := by
  change ⟪x, (w : H) - x⟫_ℂ = 0
  simp [inner_sub_right, w.property, inner_self_eq_norm_sq_to_K, hx]

/-- Translation from the affine hyperplane of representatives to the horizontal space. -/
noncomputable def translateRayHyperplane (x : H) (hx : ‖x‖ = 1) :
    {w : H // ⟪x, w⟫_ℂ = 1} ≃ₜ RayTangent x where
  toFun w := ⟨(w : H) - x, rayChart_sub_mem x hx w⟩
  invFun v := ⟨x + (v : H), inner_add_rayTangent x hx v⟩
  left_inv w := Subtype.ext (add_sub_cancel x (w : H))
  right_inv v := Subtype.ext (add_sub_cancel_left x (v : H))
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _
  continuous_invFun := (continuous_const.add continuous_subtype_val).subtype_mk _

/-- The centered chart is the affine ray chart followed by translation by `−x`. -/
noncomputable def centeredRayChart (x : H) (hx : ‖x‖ = 1) : rayChartDomain x ≃ₜ RayTangent x :=
  (rayChartHomeomorph x).trans (translateRayHyperplane x hx)

/-- The ray with centered coordinate `v`, namely `[x + v]`. -/
noncomputable def rayOfTangent (x : H) (hx : ‖x‖ = 1) (v : RayTangent x) : Projectivization ℂ H :=
  ((centeredRayChart x hx).symm v).val

theorem rayOfTangent_eq_mk (x : H) (hx : ‖x‖ = 1) (v : RayTangent x) :
    rayOfTangent x hx v = Projectivization.mk ℂ (x + (v : H)) (add_rayTangent_ne_zero x hx v) := rfl

@[simp] theorem rayOfTangent_zero (x : H) (hx : ‖x‖ = 1) :
    rayOfTangent x hx 0 = Projectivization.mk ℂ x (by intro h; simp [h] at hx) := by
  simp [rayOfTangent_eq_mk]

theorem continuous_rayOfTangent (x : H) (hx : ‖x‖ = 1) : Continuous (rayOfTangent x hx) :=
  continuous_subtype_val.comp (centeredRayChart x hx).symm.continuous

end GaussianTesting
