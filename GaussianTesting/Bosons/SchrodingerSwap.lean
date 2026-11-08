module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerCircuitSwap

@[expose] public section

/-!
# Swap and the balanced physical rotation

Swapping the two input positions after the `π/4` rotation leaves the first
output position unchanged and negates the second. On actual wavefunctions,
this gives `S U_{π/4} = U_{π/4} (I ⊗ J)`, the identity used to show that the
coherent-state accepting projection preceding Proposition 6.3 commutes with
the swap.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

private theorem balanced_swap_zero {m : ℕ} (z : BosonConfig m) :
    bosonPosition 0 (bosonRotate (Real.pi / 4) (bosonSwapPositions m z)) =
      bosonPosition 0 (bosonRotate (Real.pi / 4) z) := by
  ext j
  simp only [bosonPosition_apply, bosonRotate_zero_apply, bosonSwapPositions_zero,
    bosonSwapPositions_one, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

private theorem balanced_swap_one {m : ℕ} (z : BosonConfig m) :
    bosonPosition 1 (bosonRotate (Real.pi / 4) (bosonSwapPositions m z)) =
      -bosonPosition 1 (bosonRotate (Real.pi / 4) z) := by
  ext j
  simp only [bosonPosition_apply, bosonRotate_one_apply, bosonSwapPositions_zero,
    bosonSwapPositions_one, PiLp.neg_apply, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

private theorem balanced_swap_product (m : ℕ) (f g : WaveSpace m) :
    schrodingerCopySwap m (schrodingerRotation m (Real.pi / 4)
        (waveTensor m (hilbertTmul f g))) =
      schrodingerRotation m (Real.pi / 4) (waveTensor m (hilbertTmul f (waveParity m g))) := by
  apply Lp.ext
  have hswap := (bosonSwapPositions m).measurePreserving.quasiMeasurePreserving
  have hrot := (bosonRotation_measurePreserving m (Real.pi / 4)).quasiMeasurePreserving
  have hpos : QuasiMeasurePreserving (bosonPosition (m := m) 1) volume volume :=
    quasiMeasurePreserving_snd.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
  filter_upwards [schrodingerCopySwap_coeFn m
      (schrodingerRotation m (Real.pi / 4) (waveTensor m (hilbertTmul f g))),
    hswap.ae_eq_comp (schrodingerRotation_coeFn m (Real.pi / 4)
      (waveTensor m (hilbertTmul f g))),
    (hrot.comp hswap).ae_eq_comp (waveTensor_tmul_coeFn m f g),
    schrodingerRotation_coeFn m (Real.pi / 4)
      (waveTensor m (hilbertTmul f (waveParity m g))),
    hrot.ae_eq_comp (waveTensor_tmul_coeFn m f (waveParity m g)),
    (hpos.comp hrot).ae_eq_comp (waveParity_coeFn m g)] with z h₁ h₂ h₃ h₄ h₅ h₆
  simp only [Function.comp_apply] at h₂ h₃ h₅ h₆
  calc
    _ = f (bosonPosition 0 (bosonRotate (Real.pi / 4) (bosonSwapPositions m z))) *
        g (bosonPosition 1 (bosonRotate (Real.pi / 4) (bosonSwapPositions m z))) :=
      h₁.trans (h₂.trans h₃)
    _ = f (bosonPosition 0 (bosonRotate (Real.pi / 4) z)) *
        g (-bosonPosition 1 (bosonRotate (Real.pi / 4) z)) := by
      rw [balanced_swap_zero, balanced_swap_one]
    _ = f (bosonPosition 0 (bosonRotate (Real.pi / 4) z)) *
        waveParity m g (bosonPosition 1 (bosonRotate (Real.pi / 4) z)) :=
      congrArg (fun c : ℂ => f (bosonPosition 0 (bosonRotate (Real.pi / 4) z)) * c) h₆.symm
    _ = _ := (h₄.trans h₅).symm

/-- The physical balanced rotation turns input swap into output reflection:
`S U_{π/4} = U_{π/4} (I ⊗ J)`. -/
theorem schrodingerTensorRotation_balanced_swap (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    hilbertSwap (schrodingerTensorRotation m (Real.pi / 4) v) =
      schrodingerTensorRotation m (Real.pi / 4)
        (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
          (waveParity m).toLinearIsometry.toContinuousLinearMap v) := by
  let A := hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
    (waveParity m).toLinearIsometry.toContinuousLinearMap
  have h (w : HilbertSquare (WaveSpace m)) :
      schrodingerCopySwap m (schrodingerRotation m (Real.pi / 4) (waveTensor m w)) =
        schrodingerRotation m (Real.pi / 4) (waveTensor m (A w)) := by
    refine hilbertTensor_induction (p := fun w =>
      schrodingerCopySwap m (schrodingerRotation m (Real.pi / 4) (waveTensor m w)) =
        schrodingerRotation m (Real.pi / 4) (waveTensor m (A w)))
      (isClosed_eq ((schrodingerCopySwap m).continuous.comp
        ((schrodingerRotation m (Real.pi / 4)).continuous.comp (waveTensor m).continuous))
        ((schrodingerRotation m (Real.pi / 4)).continuous.comp
          ((waveTensor m).continuous.comp A.continuous))) ?_ ?_ w
    · intro f g
      simpa only [A, hilbertTensorMap_tmul, ContinuousLinearMap.id_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry] using
        balanced_swap_product m f g
    · intro x y hx hy
      simp only [map_add, hx, hy]
  apply (waveTensorEquiv m).injective
  have hU (w : HilbertSquare (WaveSpace m)) :
      waveTensor m (schrodingerTensorRotation m (Real.pi / 4) w) =
        schrodingerRotation m (Real.pi / 4) (waveTensor m w) := by
    exact (waveTensorEquiv m).apply_symm_apply _
  simpa only [waveTensorEquiv_apply, ← schrodingerCopySwap_waveTensor, hU] using h v

end
end GaussianTesting
