module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.RotationFixedSpace
public import GaussianTesting.Bosons.SchrodingerFourCopy
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

/-!
# Identifying the mean-zero projection with the rotation average

In the proof of Theorem 6.4, the accepting pair projection is the projection
onto the corresponding axis-invariant subspace. Here the period average of
the actual Schrödinger rotation is identified with that projection.
-/

namespace GaussianTesting

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Averaging the physical rotation over a full period is exactly the
manuscript's closed-kernel projection `P₀`. -/
theorem schrodingerP0_eq_rotationAverage (m : ℕ) (f : SchrodingerSpace m) :
    schrodingerP0 m f = schrodingerRotationAverage m f := by
  apply (schrodingerLambda m).ker.eq_starProjection_of_mem_of_inner_eq_zero
    (schrodingerRotationAverage_mem_kernel m f)
  intro w hw
  have hfix := schrodingerRotation_fixed_of_mem_kernel m hw
  have hin (t : ℝ) : inner ℂ w (schrodingerRotation m t f) = inner ℂ w f := by
    conv_lhs => lhs; rw [← hfix t]
    exact (schrodingerRotation m t).inner_map_map w f
  have havg : inner ℂ w (schrodingerRotationAverage m f) = inner ℂ w f := by
    change (innerSL ℂ w) ((2 * Real.pi)⁻¹ •
      ∫ t in 0..2 * Real.pi, schrodingerRotation m t f) = _
    rw [LinearMapClass.map_smul_of_tower, ← (innerSL ℂ w).intervalIntegral_comp_comm
      ((continuous_schrodingerRotation m f).intervalIntegrable _ _)]
    change (2 * Real.pi)⁻¹ • (∫ t in 0..2 * Real.pi,
      inner ℂ w (schrodingerRotation m t f)) = _
    simp only [hin, intervalIntegral.integral_const, sub_zero, smul_smul]
    rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_smul]
  apply inner_eq_zero_symm.mp
  rw [inner_sub_right, havg, sub_self]

/-- Strong continuity of the physical rotation in completed tensor coordinates. -/
theorem continuous_schrodingerTensorRotation (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    Continuous (fun t => schrodingerTensorRotation m t v) := by
  convert (waveTensorEquiv m).symm.continuous.comp
      (continuous_schrodingerRotation m (waveTensorEquiv m v)) using 1
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply, Function.comp_def]

/-- Joint continuity of the tensor-coordinate rotation, with vector first. -/
theorem continuous_schrodingerTensorRotation_apply (m : ℕ) :
    Continuous (fun p : HilbertSquare (WaveSpace m) × ℝ =>
      schrodingerTensorRotation m p.2 p.1) := by
  simpa only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply, Function.comp_def] using
    (waveTensorEquiv m).symm.continuous.comp
      ((continuous_schrodingerRotation_apply m).comp
        (continuous_snd.prodMk ((waveTensorEquiv m).continuous.comp continuous_fst)))

/-- The physical pair projection is the full-period rotation average,
transported to the completed tensor square of one-copy wavefunctions. -/
theorem schrodingerTensorP0_eq_rotationAverage (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorP0 m v = (2 * Real.pi)⁻¹ •
      ∫ t in 0..2 * Real.pi, schrodingerTensorRotation m t v := by
  change (waveTensorEquiv m).symm (schrodingerP0 m (waveTensorEquiv m v)) = _
  rw [schrodingerP0_eq_rotationAverage]
  change (waveTensorEquiv m).symm ((2 * Real.pi)⁻¹ •
    ∫ t in 0..2 * Real.pi, schrodingerRotation m t (waveTensorEquiv m v)) = _
  rw [map_real_smul (waveTensorEquiv m).symm (waveTensorEquiv m).symm.continuous]
  have hi := (waveTensorEquiv m).symm.toLinearIsometry.intervalIntegral_comp_comm
    (a := 0) (b := 2 * Real.pi) (μ := volume)
    (fun t => schrodingerRotation m t (waveTensorEquiv m v))
  apply congrArg (fun w => (2 * Real.pi)⁻¹ • w)
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, schrodingerTensorRotation,
    LinearIsometryEquiv.trans_apply] using hi.symm

end
end GaussianTesting
