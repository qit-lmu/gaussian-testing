module

public import GaussianTesting.GradientFlow.FubiniStudyGradient
public import GaussianTesting.GradientFlow.Contraction

@[expose] public section

/-! # Critical points of acceptance and the contracted operator

The unnumbered claim after Lemma 3.1 identifies critical points of acceptance
on projective Hilbert space with the eigenvector equation for `K_ψ`.
The differential below is taken in the centered projective chart, so its
vanishing is the manuscript's critical-point condition.
-/

namespace GaussianTesting

namespace TensorSquare

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K}

/-- A ray is critical for acceptance exactly when its horizontal gradient
vanishes. The differential is taken in its centered projective chart. -/
theorem fderiv_rayAcceptance_eq_zero_iff_gradAccA_eq_zero (hP : T.IsAcceptance P)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    fderiv ℝ (fun v : RayTangent ψ => T.rayAcceptance P (rayOfTangent ψ hψ v)) 0 = 0 ↔
      T.gradAccA P ψ = 0 := by
  constructor
  · intro hd
    have hg := (T.isFubiniStudyGradient_iff hP hψ (0 : RayTangent ψ)).mp
      (by intro v; simp [hd, rayTangentMetric])
    simpa using hg.symm
  · intro hg
    have hd := (T.isFubiniStudyGradient_iff hP hψ (0 : RayTangent ψ)).mpr
      (by simpa using hg.symm)
    ext v
    simpa [rayTangentMetric] using hd v

/-- The critical-point characterization after Lemma 3.1: the projective
differential vanishes exactly when `ψ` is a `K_ψ` eigenvector at acceptance. -/
theorem fderiv_rayAcceptance_eq_zero_iff_contractionOperator (hP : T.IsAcceptance P)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    fderiv ℝ (fun v : RayTangent ψ => T.rayAcceptance P (rayOfTangent ψ hψ v)) 0 = 0 ↔
      T.contractionOperator P ψ ψ = (T.accProbA P ψ : ℂ) • ψ :=
  (T.fderiv_rayAcceptance_eq_zero_iff_gradAccA_eq_zero hP hψ).trans
    (T.gradAccA_eq_zero_iff_contractionOperator ψ)

end TensorSquare

/-- The manuscript's critical-point characterization on the completed tensor
square of any complex Hilbert space, including infinite-dimensional spaces. -/
theorem contraction_criticalPoint_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) {ψ : H} (hψ : ‖ψ‖ = 1) :
    fderiv ℝ (fun v : RayTangent ψ =>
      (hilbertTensorSquare H).rayAcceptance P (rayOfTangent ψ hψ v)) 0 = 0 ↔
      (hilbertTensorSquare H).contractionOperator P ψ ψ =
        ((hilbertTensorSquare H).accProbA P ψ : ℂ) • ψ :=
  (hilbertTensorSquare H).fderiv_rayAcceptance_eq_zero_iff_contractionOperator hP hψ

end GaussianTesting
