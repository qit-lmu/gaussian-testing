module

public import GaussianTesting.GradientFlow.RayTangentChart
public import GaussianTesting.GradientFlow.RaySpeed
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Fubini–Study metric in a centered affine chart

At the ray of a unit vector `x`, tangent vectors are the complex orthogonal
complement of `x`. A differentiable curve in these coordinates has
Fubini–Study speed equal to the Hilbert norm of its velocity. Polarization
therefore gives the real part of the inner product as the metric tensor
in the manuscript's normalization.
-/

@[expose] public section

namespace GaussianTesting

open Filter Set Topology
open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Fubini–Study metric on horizontal tangent representatives at the ray of `x`. -/
def rayTangentMetric (x : H) (v w : RayTangent x) : ℝ := (inner ℂ (v : H) (w : H)).re

/-- In horizontal coordinates the metric is the real Hilbert inner product. -/
theorem rayTangentMetric_eq_real_inner (x : H) (v w : RayTangent x) :
    rayTangentMetric x v w = inner ℝ v w := rfl

/-- Riesz duality for the horizontal tangent Hilbert space evaluates by the
Fubini–Study metric. -/
theorem toDual_rayTangent_apply [CompleteSpace H] (x : H) (v w : RayTangent x) :
    InnerProductSpace.toDual ℝ (RayTangent x) v w = rayTangentMetric x v w := rfl

/-- The real polarization identity recovers the metric from its tangent norm. -/
theorem rayTangentMetric_eq_polarization (x : H) (v w : RayTangent x) :
    rayTangentMetric x v w = (‖v + w‖ ^ 2 - ‖v‖ ^ 2 - ‖w‖ ^ 2) / 2 := by
  change (inner ℂ (v : H) (w : H)).re =
    (‖(v : H) + (w : H)‖ ^ 2 - ‖(v : H)‖ ^ 2 - ‖(w : H)‖ ^ 2) / 2
  rw [@norm_add_sq ℂ]
  change _ = (‖(v : H)‖ ^ 2 + 2 * (inner ℂ (v : H) (w : H)).re + ‖(w : H)‖ ^ 2 -
    ‖(v : H)‖ ^ 2 - ‖(w : H)‖ ^ 2) / 2
  ring

/-- Transport a tangent representative together with its base representative. -/
def rayTangentPhase (z : ℂ) (x : H) (v : RayTangent x) : RayTangent (z • x) :=
  ⟨z • (v : H), by
    change inner ℂ (z • x) (z • (v : H)) = 0
    simp [inner_smul_left, inner_smul_right, (show inner ℂ x (v : H) = 0 from v.property)]⟩

/-- Centered coordinates at phase-related representatives give the very same
ray when the coordinate vector changes by that phase. -/
theorem rayOfTangent_phase (x : H) (hx : ‖x‖ = 1) {z : ℂ} (hz : ‖z‖ = 1) (v : RayTangent x) :
    rayOfTangent (z • x) (by simp [norm_smul, hz, hx]) (rayTangentPhase z x v) =
      rayOfTangent x hx v := by
  rw [rayOfTangent_eq_mk, rayOfTangent_eq_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨z, smul_add z x (v : H)⟩

/-- Changing the phase of a unit representative preserves the metric. -/
theorem rayTangentMetric_phase (x : H) {z : ℂ} (hz : ‖z‖ = 1) (v w : RayTangent x) :
    rayTangentMetric (z • x) (rayTangentPhase z x v) (rayTangentPhase z x w) =
      rayTangentMetric x v w := by
  change (inner ℂ (z • (v : H)) (z • (w : H))).re = _
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hz]
  simp [rayTangentMetric]

private theorem norm_add_tangent (x : H) (hx : ‖x‖ = 1) (v : RayTangent x) :
    ‖x + (v : H)‖ = Real.sqrt (1 + ‖v‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (x + (v : H))), @norm_add_sq ℂ]
  simp [hx, (show inner ℂ x (v : H) = 0 from v.property)]

set_option backward.isDefEq.respectTransparency false in
/-- The unit section over the centered chart has derivative equal to the inclusion
of the horizontal tangent space. -/
theorem hasFDerivAt_rayTangentSection_zero (x : H) (hx : ‖x‖ = 1) :
    HasFDerivAt (fun v : RayTangent x => rayChartSection (x + (v : H)))
      ((innerSL ℂ x).ker.subtypeL.restrictScalars ℝ) 0 := by
  have hs : HasFDerivAt (fun v : RayTangent x => 1 + ‖v‖ ^ 2) (0 : RayTangent x →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : RayTangent x)).hasFDerivAt.const_add (1 : ℝ)
  have hn : HasFDerivAt (fun v : RayTangent x => ‖x + (v : H)‖) (0 : RayTangent x →L[ℝ] ℝ) 0 := by
    simpa [norm_add_tangent x hx] using hs.sqrt (by simp)
  have hc : HasFDerivAt (fun v : RayTangent x => (‖x + (v : H)‖ : ℂ)⁻¹) (0 : RayTangent x →L[ℝ] ℂ) 0 := by
    have hne : ‖x + ((0 : RayTangent x) : H)‖ ≠ 0 := by simp [hx]
    have hinv := (hasDerivAt_inv hne).comp_hasFDerivAt (0 : RayTangent x) hn
    simpa [Function.comp_def] using Complex.ofRealCLM.hasFDerivAt.comp (0 : RayTangent x) hinv
  have ha := ((innerSL ℂ x).ker.subtypeL.restrictScalars ℝ).hasFDerivAt (x := 0) |>.const_add x
  change HasFDerivAt ((fun v : RayTangent x => (‖x + (v : H)‖ : ℂ)⁻¹) •
    fun v : RayTangent x => x + (v : H)) _ 0
  simpa [hx] using! hc.smul ha

/-- The Fubini–Study distance quotient of a curve passing through the chart
center converges to the Hilbert norm of its chart velocity. -/
theorem tendsto_dist_div_time_rayOfTangent (x : H) (hx : ‖x‖ = 1)
    {c : ℝ → RayTangent x} {s : Set ℝ} {t : ℝ} (ht : t ∈ s) (hct : c t = 0)
    {v : RayTangent x} (hc : HasDerivWithinAt c v s t) :
    Tendsto (fun r => dist (rayOfTangent x hx (c r)) (rayOfTangent x hx (c t)) / |r - t|)
      (𝓝[s \ {t}] t) (𝓝 ‖v‖) := by
  let γ (r : ℝ) := rayChartSection (x + (c r : H))
  have hbase : γ t = x := by simp [γ, hct, rayChartSection, hx]
  have hd : HasDerivWithinAt γ (v : H) s t := by
    have hD := hasFDerivAt_rayTangentSection_zero x hx
    rw [← hct] at hD
    exact hD.comp_hasDerivWithinAt t hc
  have hn (r : ℝ) := add_rayTangent_ne_zero x hx (c r)
  apply tendsto_dist_div_time_of_horizontal_lift (γ := γ) ht hd
  · rw [hbase]
    exact v.property
  · exact fun r _ => norm_rayChartSection _ (hn r)
  · intro r _ hγ
    rw [rayOfTangent_eq_mk]
    exact (mk_rayChartSection _ (hn r)).symm
  · exact ((continuous_rayOfTangent x hx).continuousAt.comp_continuousWithinAt hc.continuousWithinAt)

/-- Every horizontal tangent vector occurs as the velocity of a centered
chart line, whose distance quotient converges to the norm of that vector. -/
theorem tendsto_dist_div_time_rayTangent_line (x : H) (hx : ‖x‖ = 1) (v : RayTangent x) :
    Tendsto (fun r : ℝ => dist (rayOfTangent x hx (r • v)) (rayOfTangent x hx 0) / |r|)
      (𝓝[≠] 0) (𝓝 ‖v‖) := by
  have hc : HasDerivAt (fun r : ℝ => r • v) v 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).smul_const v
  simpa [← Set.compl_eq_univ_sdiff] using tendsto_dist_div_time_rayOfTangent x hx
    (Set.mem_univ (0 : ℝ)) (zero_smul ℝ v) hc.hasDerivWithinAt

/-- Polarizing squared Fubini–Study distance quotients along chart lines
recovers the real inner product on the whole horizontal tangent space. -/
theorem tendsto_rayTangentMetric_of_dist (x : H) (hx : ‖x‖ = 1) (v w : RayTangent x) :
    let speed := fun (r : ℝ) (u : RayTangent x) =>
      dist (rayOfTangent x hx (r • u)) (rayOfTangent x hx 0) / |r|
    Tendsto (fun r : ℝ => (speed r (v + w) ^ 2 - speed r v ^ 2 - speed r w ^ 2) / 2)
      (𝓝[≠] 0) (𝓝 (rayTangentMetric x v w)) := by
  rw [rayTangentMetric_eq_polarization]
  have h (u : RayTangent x) := (tendsto_dist_div_time_rayTangent_line x hx u).pow 2
  exact (((h (v + w)).sub (h v)).sub (h w)).div_const 2

end
end GaussianTesting
