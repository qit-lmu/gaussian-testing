module

public import GaussianTesting.GradientFlow.FubiniStudy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Speed of a horizontal lift in the Fubini–Study metric

To identify the squared speed in Eq. (3.7), measure distance along the ray
curve itself. The sine of the angle to a fixed ray is the norm of the
component perpendicular to its unit representative. At the base time the
velocity of a horizontal lift lies entirely in that perpendicular space.
-/

@[expose] public section

namespace GaussianTesting

open Filter Set Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private noncomputable def perpComponent (x : H) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (ContinuousLinearMap.toSpanSingleton ℂ x).comp (innerSL ℂ x)

private theorem perpComponent_apply (x y : H) :
    perpComponent x y = y - ⟪x, y⟫_ℂ • x := rfl

private theorem sin_angle_eq_norm_perpComponent (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.sin (Real.arccos ‖⟪x, y⟫_ℂ‖) = ‖perpComponent x y‖ := by
  rw [Real.sin_arccos, Real.sqrt_eq_iff_mul_self_eq (by
    have h := norm_inner_le_norm (𝕜 := ℂ) x y
    rw [hx, hy, one_mul] at h
    nlinarith [norm_nonneg (⟪x, y⟫_ℂ)]) (norm_nonneg _)]
  rw [← sq, perpComponent_apply, @norm_sub_sq ℂ, norm_smul, hx, hy, mul_one, inner_smul_right,
    ← inner_conj_symm x y, Complex.conj_mul', Complex.norm_conj]
  simp only [RCLike.re_eq_complex_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-- For a differentiable unit lift whose velocity is horizontal at `t`, the
Fubini–Study speed of its ray at `t` is the norm of that velocity. -/
theorem tendsto_dist_div_time_of_horizontal_lift
    {γ : ℝ → H} {ρ : ℝ → Projectivization ℂ H} {s : Set ℝ} {t : ℝ} {v : H}
    (ht : t ∈ s) (hd : HasDerivWithinAt γ v s t) (horizontal : ⟪γ t, v⟫_ℂ = 0)
    (hunit : ∀ r ∈ s, ‖γ r‖ = 1)
    (hrep : ∀ r ∈ s, ∀ hn : γ r ≠ 0, ρ r = Projectivization.mk ℂ (γ r) hn)
    (hcont : ContinuousWithinAt ρ s t) :
    Tendsto (fun r => dist (ρ r) (ρ t) / |r - t|) (𝓝[s \ {t}] t) (𝓝 ‖v‖) := by
  let W := perpComponent (γ t)
  have hW : W (γ t) = 0 := by simp [W, perpComponent_apply, inner_self_eq_norm_sq_to_K, hunit t ht]
  have hv : W v = v := by simp [W, perpComponent_apply, horizontal]
  have hD := (W.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hd
  change HasDerivWithinAt (fun r => W (γ r)) (W v) s t at hD
  rw [hv] at hD
  have hratio : Tendsto (fun r => ‖W (γ r)‖ / |r - t|) (𝓝[s \ {t}] t) (𝓝 ‖v‖) := by
    simpa only [slope_def_module, hW, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, div_eq_inv_mul]
      using (hasDerivWithinAt_iff_tendsto_slope.mp hD).norm
  let d (r : ℝ) := dist (ρ r) (ρ t)
  have hd0 : Tendsto d (𝓝[s \ {t}] t) (𝓝 0) := by
    simpa only [d, dist_self] using (hcont.dist (tendsto_const_nhds (x := ρ t))).mono_left
      (nhdsWithin_mono t sdiff_subset)
  have hsinc : Tendsto (fun r => Real.sinc (d r)) (𝓝[s \ {t}] t) (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using Real.continuous_sinc.continuousAt.tendsto.comp hd0
  have hquot := hratio.div hsinc one_ne_zero
  rw [div_one] at hquot
  apply (hquot.congr' ?_)
  filter_upwards [self_mem_nhdsWithin, hsinc.eventually_ne one_ne_zero] with r hr hn
  have unit_ne (u : ℝ) (hu : u ∈ s) : γ u ≠ 0 := by intro he; simpa [he] using hunit u hu
  have hsin : Real.sin (d r) = ‖W (γ r)‖ := by
    dsimp only [d]
    rw [dist_comm, dist_ray_eq, hrep t ht (unit_ne t ht), hrep r hr.1 (unit_ne r hr.1),
      rayDist_mk _ _ (hunit t ht) (hunit r hr.1)]
    exact sin_angle_eq_norm_perpComponent _ _ (hunit t ht) (hunit r hr.1)
  change (‖W (γ r)‖ / |r - t|) / Real.sinc (d r) = d r / |r - t|
  rw [← hsin]
  by_cases hz : d r = 0
  · simp [hz]
  · rw [Real.sinc_of_ne_zero hz] at hn ⊢
    have hsin_ne : Real.sin (d r) ≠ 0 := fun h => hn (by rw [h, zero_div])
    field_simp

end GaussianTesting
