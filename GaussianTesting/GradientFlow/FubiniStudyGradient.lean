module

public import GaussianTesting.GradientFlow.HilbertTensor
public import GaussianTesting.GradientFlow.RayDifferential
public import GaussianTesting.GradientFlow.RayTangentMetric

@[expose] public section

/-! # The Fubini–Study gradient of acceptance (Eq. (3.4))

At each unit representative the centered chart parametrizes nearby rays by its
complex orthogonal complement. The norm of a tangent vector in these coordinates
is its Fubini–Study speed. The real differential of acceptance therefore has a
unique metric dual, computed below from the product rule and swap symmetry.
-/

namespace GaussianTesting

namespace TensorSquare

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K}

/-- In the centered chart at a unit representative, the horizontal field
of Eq. (3.4) is the gradient of acceptance for the Fubini–Study metric. -/
theorem hasGradientAt_rayAcceptance (hP : T.IsAcceptance P) {x : H} (hx : ‖x‖ = 1) :
    HasGradientAt (fun v : RayTangent x => T.rayAcceptance P (rayOfTangent x hx v))
      (⟨T.gradAccA P x, T.inner_gradAccA_eq_zero hP hx⟩ : RayTangent x) 0 := by
  let ι := (innerSL ℂ x).ker.subtypeL.restrictScalars ℝ
  have hchart : HasFDerivAt (fun v : RayTangent x => x + (v : H)) ι 0 :=
    ι.hasFDerivAt.const_add x
  have hnormalize : HasFDerivAt (fun y => T.accProbA P (rayChartSection y))
      (Complex.reCLM.comp (((innerSL ℂ) (T.gradAccA P x)).restrictScalars ℝ))
      (x + ((0 : RayTangent x) : H)) := by
    simpa only [Submodule.coe_zero, add_zero] using T.hasFDerivAt_accProbA_rayChartSection hP hx
  have hd := hnormalize.comp (f := fun v : RayTangent x => x + (v : H)) 0 hchart
  rw [hasGradientAt_iff_hasFDerivAt]
  have hfun : (fun v : RayTangent x => T.rayAcceptance P (rayOfTangent x hx v)) =
      (fun y => T.accProbA P (rayChartSection y)) ∘ (fun v : RayTangent x => x + (v : H)) := by
    funext v
    rw [rayOfTangent_eq_mk, T.rayAcceptance_mk_eq_accProbA_rayChartSection]
    rfl
  rw [hfun]
  apply hd.congr_fderiv
  ext v
  rfl

/-- The explicit field is the unique horizontal vector pairing with the
differential on every tangent vector, without reference to a trajectory. -/
theorem isFubiniStudyGradient_iff (hP : T.IsAcceptance P) {x : H} (hx : ‖x‖ = 1)
    (w : RayTangent x) :
    (∀ v : RayTangent x,
      fderiv ℝ (fun u : RayTangent x => T.rayAcceptance P (rayOfTangent x hx u)) 0 v =
        rayTangentMetric x w v) ↔ (w : H) = T.gradAccA P x := by
  let G : RayTangent x := ⟨T.gradAccA P x, T.inner_gradAccA_eq_zero hP hx⟩
  have hd := T.hasGradientAt_rayAcceptance hP hx
  have hp (v : RayTangent x) :
      fderiv ℝ (fun u : RayTangent x => T.rayAcceptance P (rayOfTangent x hx u)) 0 v =
        rayTangentMetric x G v := hd.fderiv_apply
  constructor
  · intro hw
    have he : InnerProductSpace.toDual ℝ (RayTangent x) w =
        InnerProductSpace.toDual ℝ (RayTangent x) G := by
      ext v
      exact ((hw v).symm.trans (hp v))
    exact congrArg Subtype.val ((InnerProductSpace.toDual ℝ (RayTangent x)).injective he)
  · intro hw
    have he : w = G := Subtype.ext hw
    simpa only [he] using hp

/-- The gradient in a different unit representative's centered chart is the
same tangent vector transported by that phase. -/
theorem gradient_rayAcceptance_phase (hP : T.IsAcceptance P) {x : H} (hx : ‖x‖ = 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    let hzx : ‖z • x‖ = 1 := by simp [norm_smul, hz, hx]
    gradient (fun v => T.rayAcceptance P (rayOfTangent (z • x) hzx v)) 0 =
      rayTangentPhase z x (gradient (fun v => T.rayAcceptance P (rayOfTangent x hx v)) 0) := by
  dsimp only
  rw [(T.hasGradientAt_rayAcceptance hP (show ‖z • x‖ = 1 by simp [norm_smul, hz, hx])).gradient,
    (T.hasGradientAt_rayAcceptance hP hx).gradient]
  exact Subtype.ext (T.gradAccA_phase P z hz x)

end TensorSquare

/-- Eq. (3.4) on the completed Hilbert tensor square. For every unit
representative, the gradient is four times the contraction of the projected
tensor square minus its radial component. -/
theorem fubiniStudyGradient_rayAcceptance {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) {x : H} (hx : ‖x‖ = 1) :
    let T := hilbertTensorSquare H
    HasGradientAt (fun v : RayTangent x => T.rayAcceptance P (rayOfTangent x hx v))
      (⟨(4 : ℂ) • (T.contr x (P (hilbertTmul x x)) - (T.accProbA P x : ℂ) • x),
        T.inner_gradAccA_eq_zero hP hx⟩ : RayTangent x) 0 :=
  (hilbertTensorSquare H).hasGradientAt_rayAcceptance hP hx

end GaussianTesting
