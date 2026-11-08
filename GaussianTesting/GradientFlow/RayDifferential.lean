module

public import GaussianTesting.GradientFlow.ProjectiveEnergy

@[expose] public section

/-!
# Differential of acceptance on normalized representatives

The manuscript computes the ambient derivative using the product rule and swap
symmetry. Normalization removes its radial component. The resulting real
differential, evaluated at a unit representative, is pairing against the
horizontal field in Eq. (3.4).
-/

namespace GaussianTesting.TensorSquare

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K}

omit [CompleteSpace H] [CompleteSpace K] in
/-- On a nonzero representative the ray acceptance is the ambient acceptance
after normalization. -/
theorem rayAcceptance_mk_eq_accProbA_rayChartSection (T : TensorSquare H K) (P : K →L[ℂ] K)
    (y : H) (hy : y ≠ 0) :
    T.rayAcceptance P (Projectivization.mk ℂ y hy) = T.accProbA P (rayChartSection y) := by
  rw [← mk_rayChartSection y hy]
  exact T.rayAcceptance_mk P _ (norm_rayChartSection y hy) _

omit [CompleteSpace H] [CompleteSpace K] in
private theorem accProbA_rayChartSection (T : TensorSquare H K) (P : K →L[ℂ] K) (y : H) :
    T.accProbA P (rayChartSection y) = T.accProbA P y / (‖y‖ ^ 2) ^ 2 := by
  let c : ℂ := (‖y‖ : ℂ)⁻¹
  have hc : starRingEnd ℂ c = c := by simp [c]
  have hscale : ⟪T.tp (c • y) (c • y), P (T.tp (c • y) (c • y))⟫_ℂ =
      ((‖y‖⁻¹ ^ 4 : ℝ) : ℂ) * ⟪T.tp y y, P (T.tp y y)⟫_ℂ := by
    simp only [map_smul, smul_apply, inner_smul_left, inner_smul_right, hc]
    push_cast
    change c * (c * (c * (c * _))) = c ^ 4 * _
    ring
  change (⟪T.tp (c • y) (c • y), P (T.tp (c • y) (c • y))⟫_ℂ).re = _
  rw [hscale]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [accProbA, div_eq_mul_inv, ← inv_pow, ← pow_mul]
  ring

/-- At a unit representative the real Fréchet differential of normalized
acceptance is the real inner product with the field in Eq. (3.4). -/
theorem hasFDerivAt_accProbA_rayChartSection (hP : T.IsAcceptance P) {x : H} (hx : ‖x‖ = 1) :
    HasFDerivAt (fun y => T.accProbA P (rayChartSection y))
      (Complex.reCLM.comp (((innerSL ℂ) (T.gradAccA P x)).restrictScalars ℝ)) x := by
  let _ := InnerProductSpace.rclikeToReal ℂ H
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hi := (hasDerivAt_inv (show ‖x‖ ^ 2 * ‖x‖ ^ 2 ≠ 0 by simp [hx])).comp_hasFDerivAt x (hn.mul hn)
  have hd := (T.hasFDerivAt_accProbA hP x).mul hi
  simp_rw [T.accProbA_rayChartSection P, sq (‖_‖ ^ 2), div_eq_mul_inv]
  apply hd.congr_fderiv
  ext v
  simp [hx, TensorSquare.gradAccA, real_inner_eq_re_inner ℂ, inner_smul_left_eq_smul, Complex.mul_re]
  ring

end GaussianTesting.TensorSquare
