module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerFourCopy

@[expose] public section

/-!
# Swapping the outputs of opposite-angle beam splitters

Swapping the two registers conjugates the physical coordinate rotation to
its inverse. On two identical inputs the positive-angle splitter therefore
produces the swapped negative-angle output. These identities identify the
difference output and its parity in the balanced-splitter constructions.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

def bosonSwapPositions (m : ℕ) : BosonConfig m ≃ₗᵢ[ℝ] BosonConfig m :=
  (splitConfigIsometry m).trans
    ((LinearIsometryEquiv.withLpProdComm 2 ℝ (WaveConfig m) (WaveConfig m)).trans
      (splitConfigIsometry m).symm)

theorem bosonSwapPositions_zero {m : ℕ} (z : BosonConfig m) (j : Fin m) :
    bosonSwapPositions m z (0, j) = z (1, j) := rfl

theorem bosonSwapPositions_one {m : ℕ} (z : BosonConfig m) (j : Fin m) :
    bosonSwapPositions m z (1, j) = z (0, j) := rfl

theorem bosonPosition_swap_zero {m : ℕ} (z : BosonConfig m) :
    bosonPosition 0 (bosonSwapPositions m z) = bosonPosition 1 z := by
  ext j
  exact bosonSwapPositions_zero z j

theorem bosonPosition_swap_one {m : ℕ} (z : BosonConfig m) :
    bosonPosition 1 (bosonSwapPositions m z) = bosonPosition 0 z := by
  ext j
  exact bosonSwapPositions_one z j

def schrodingerCopySwap (m : ℕ) : SchrodingerSpace m →ₗᵢ[ℂ] SchrodingerSpace m :=
  Lp.compMeasurePreservingₗᵢ ℂ (bosonSwapPositions m) (bosonSwapPositions m).measurePreserving

theorem schrodingerCopySwap_coeFn (m : ℕ) (f : SchrodingerSpace m) :
    (schrodingerCopySwap m f : BosonConfig m → ℂ) =ᵐ[volume]
      fun z => f (bosonSwapPositions m z) :=
  Lp.coeFn_compMeasurePreserving f (bosonSwapPositions m).measurePreserving

theorem schrodingerCopySwap_waveTensor (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    schrodingerCopySwap m (waveTensor m v) = waveTensor m (hilbertSwap v) := by
  refine hilbertTensor_induction (p := fun v =>
    schrodingerCopySwap m (waveTensor m v) = waveTensor m (hilbertSwap v))
    (isClosed_eq ((schrodingerCopySwap m).continuous.comp (waveTensor m).continuous)
      ((waveTensor m).continuous.comp hilbertSwap.continuous)) ?_ ?_ v
  · intro f g
    rw [hilbertSwap_tmul]
    apply Lp.ext
    filter_upwards [schrodingerCopySwap_coeFn m (waveTensor m (hilbertTmul f g)),
      (bosonSwapPositions m).measurePreserving.quasiMeasurePreserving.ae_eq_comp
        (waveTensor_tmul_coeFn m f g), waveTensor_tmul_coeFn m g f] with z hz hz' hz''
    simp only [Function.comp_apply, bosonPosition_swap_zero z, bosonPosition_swap_one z] at hz'
    exact hz.trans (hz'.trans ((mul_comm
      (f (bosonPosition 1 z)) (g (bosonPosition 0 z))).trans hz''.symm))
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem bosonRotate_swap (m : ℕ) (θ : ℝ) (z : BosonConfig m) :
    bosonRotate θ (bosonSwapPositions m z) = bosonSwapPositions m (bosonRotate (-θ) z) := by
  ext ⟨i,j⟩
  fin_cases i <;> simp [bosonSwapPositions_zero, bosonSwapPositions_one] <;> ring

theorem schrodingerCopySwap_rotation (m : ℕ) (θ : ℝ) (f : SchrodingerSpace m) :
    schrodingerCopySwap m (schrodingerRotation m θ f) =
      schrodingerRotation m (-θ) (schrodingerCopySwap m f) := by
  apply Lp.ext
  have hs := (bosonSwapPositions m).measurePreserving.quasiMeasurePreserving
  have hr := (bosonRotation_measurePreserving m (-θ)).quasiMeasurePreserving
  filter_upwards [schrodingerCopySwap_coeFn m (schrodingerRotation m θ f),
    hs.ae_eq_comp (schrodingerRotation_coeFn m θ f),
    schrodingerRotation_coeFn m (-θ) (schrodingerCopySwap m f),
    hr.ae_eq_comp (schrodingerCopySwap_coeFn m f)] with z h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂ h₄
  rw [bosonRotate_swap] at h₂
  exact (h₁.trans h₂).trans (h₃.trans h₄).symm

/-- Register swap reverses the sign of the physical beam-splitter angle. -/
theorem schrodingerTensorRotation_swap (m : ℕ) (θ : ℝ)
    (v : HilbertSquare (WaveSpace m)) :
    hilbertSwap (schrodingerTensorRotation m θ v) =
      schrodingerTensorRotation m (-θ) (hilbertSwap v) := by
  apply (waveTensorEquiv m).injective
  change waveTensor m (hilbertSwap (schrodingerTensorRotation m θ v)) =
    waveTensorEquiv m (schrodingerTensorRotation m (-θ) (hilbertSwap v))
  rw [← schrodingerCopySwap_waveTensor]
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change schrodingerCopySwap m ((waveTensorEquiv m) ((waveTensorEquiv m).symm
    (schrodingerRotation m θ (waveTensorEquiv m v)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, schrodingerCopySwap_rotation]
  exact congrArg (schrodingerRotation m (-θ)) (schrodingerCopySwap_waveTensor m v)

/-- The inverse physical rotation is the negative-angle rotation. -/
theorem schrodingerTensorRotation_symm (m : ℕ) (θ : ℝ) :
    (schrodingerTensorRotation m θ).symm = schrodingerTensorRotation m (-θ) := by
  ext v
  apply (schrodingerTensorRotation m θ).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, schrodingerTensorRotation,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    schrodingerRotation_neg_right]
  exact ((waveTensorEquiv m).symm_apply_apply v).symm

/-- On identical inputs, swapping the positive-angle output gives exactly
the negative-angle output, including the retained difference register. -/
theorem schrodingerTensorRotation_swap_identical (m : ℕ) (θ : ℝ) (ψ : WaveSpace m) :
    hilbertSwap (schrodingerTensorRotation m θ (hilbertTmul ψ ψ)) =
      (schrodingerTensorRotation m θ).symm (hilbertTmul ψ ψ) := by
  calc
    _ = schrodingerTensorRotation m (-θ) (hilbertSwap (hilbertTmul ψ ψ)) :=
      schrodingerTensorRotation_swap m θ (hilbertTmul ψ ψ)
    _ = schrodingerTensorRotation m (-θ) (hilbertTmul ψ ψ) :=
      congrArg (schrodingerTensorRotation m (-θ)) (hilbertSwap_tmul ψ ψ)
    _ = _ := congrArg (fun U : HilbertSquare (WaveSpace m) ≃ₗᵢ[ℂ]
      HilbertSquare (WaveSpace m) => U (hilbertTmul ψ ψ))
      (schrodingerTensorRotation_symm m θ).symm

end
end GaussianTesting
