module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.GradientFlow.HilbertTensor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

/-!
# Tensoring the rotation-fixed projection

The proof of Theorem 6.4 identifies each pair projection with an axis-fixed
projection. A spectator tensor factor commutes with the period average, so
this identification extends to entangled vectors in the completed tensor product.
-/

namespace GaussianTesting

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- A period-average projection on one factor is the fixed-space projection
for the corresponding unitary action with a spectator factor. -/
theorem tensor_rotation_fixedProjection
    (U : ℝ → B ≃ₗᵢ[ℂ] B)
    (hU : ∀ b, Continuous (fun t => U t b))
    (R : ℝ → HilbertTensor A B ≃ₗᵢ[ℂ] HilbertTensor A B)
    (hR : Continuous (fun p : HilbertTensor A B × ℝ => R p.2 p.1))
    (htensor : ∀ t a b, R t (hilbertTmul a b) = hilbertTmul a (U t b))
    (P : B →L[ℂ] B)
    (hP : ∀ b, P b = (2 * Real.pi)⁻¹ • ∫ t in 0..2 * Real.pi, U t b)
    (hUP : ∀ t b, U t (P b) = P b)
    (F : Submodule ℂ (HilbertTensor A B)) [CompleteSpace F]
    (hF : ∀ v, v ∈ F ↔ ∀ t, R t v = v) :
    F.starProjection = hilbertTensorMap (ContinuousLinearMap.id ℂ A) P := by
  let T := hilbertTensorMap (ContinuousLinearMap.id ℂ A) P
  let avg := fun v : HilbertTensor A B =>
    (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • ∫ t in 0..2 * Real.pi, R t v
  have hcont : Continuous avg :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v t => R t v) hR 0 (2 * Real.pi)).const_smul
        (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  have hint (v : HilbertTensor A B) :
      IntervalIntegrable (fun t => R t v) volume 0 (2 * Real.pi) :=
    (hR.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have havg (v : HilbertTensor A B) : T v = avg v := by
    apply hilbertTensor_induction (p := fun w => T w = avg w)
      (isClosed_eq T.continuous hcont) _ _ v
    · intro a b
      dsimp only [T]
      rw [hilbertTensorMap_tmul, ContinuousLinearMap.id_apply]
      rw [hP b]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
        ← (hilbertTmul a).intervalIntegral_comp_comm
        ((hU b).intervalIntegrable _ _)]
      simp only [avg, htensor]
      rfl
    · intro v w hv hw
      simp only [avg, map_add, intervalIntegral.integral_add (hint v) (hint w), smul_add]
        at hv hw ⊢
      exact congrArg₂ (· + ·) hv hw
  have hfixed (t : ℝ) (v : HilbertTensor A B) : R t (T v) = T v := by
    apply hilbertTensor_induction (p := fun w => R t (T w) = T w)
      (isClosed_eq ((R t).continuous.comp T.continuous) T.continuous) _ _ v
    · intro a b
      simp only [T, hilbertTensorMap_tmul, ContinuousLinearMap.id_apply, htensor, hUP]
    · intro v w hv hw
      simp only [map_add, hv, hw]
  ext v : 1
  apply F.eq_starProjection_of_mem_of_inner_eq_zero ((hF _).mpr (fun t => hfixed t v))
  intro w hw
  have hwfix := (hF w).mp hw
  have hin (t : ℝ) : inner ℂ w (R t v) = inner ℂ w v := by
    conv_lhs => lhs; rw [← hwfix t]
    exact (R t).inner_map_map w v
  have hinavg : inner ℂ w (avg v) = inner ℂ w v := by
    change (innerSL ℂ w) ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
      ∫ t in 0..2 * Real.pi, R t v) = _
    rw [map_smul, ← (innerSL ℂ w).intervalIntegral_comp_comm (hint v)]
    change (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
      (∫ t in 0..2 * Real.pi, inner ℂ w (R t v)) = _
    simp only [hin, intervalIntegral.integral_const, sub_zero]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    change ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) • inner ℂ w v = _
    rw [← Complex.ofReal_mul,
      inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), Complex.ofReal_one, one_smul]
  apply inner_eq_zero_symm.mp
  change inner ℂ w (v - T v) = 0
  rw [inner_sub_right, havg, hinavg, sub_self]

end
end GaussianTesting
