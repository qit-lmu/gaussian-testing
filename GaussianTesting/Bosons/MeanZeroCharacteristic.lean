module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.WeylRotation
public import GaussianTesting.Bosons.CharacteristicEquation

@[expose] public section

/-!
# The characteristic-function argument in Proposition 6.1

The actual closed-kernel test fixes every copy rotation. On a tensor square,
Weyl covariance gives the manuscript's balanced-rotation equation. Continuity,
positivity, and polarization then give a centered Gaussian characteristic
function, without a moment assumption. The independent Gaussian-state
characterizations are not assumed by this argument.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Every copy rotation fixes the range of the physical closed-kernel test,
also in completed-tensor coordinates. -/
theorem schrodingerTensorRotation_P0 (m : ℕ) (θ : ℝ)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorRotation m θ (schrodingerTensorP0 m v) =
      schrodingerTensorP0 m v := by
  apply (waveTensorEquiv m).injective
  simp only [schrodingerTensorRotation, schrodingerTensorP0,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    schrodingerRotation_P0]

/-- Equation (chi-rotation) follows from membership in the actual closed
kernel, using the manuscript's balanced copy rotation. -/
theorem pureWaveCharacteristic_balanced_of_kernel {m : ℕ} {ψ : WaveSpace m}
    (hψ : schrodingerTensorP0 m (hilbertTmul ψ ψ) = hilbertTmul ψ ψ) :
    BalancedCharacteristicEquation (pureWaveCharacteristic m ψ) := by
  have hf : schrodingerTensorRotation m (Real.pi/4) (hilbertTmul ψ ψ) =
      hilbertTmul ψ ψ := by
    simpa only [hψ] using schrodingerTensorRotation_P0 m (Real.pi/4) (hilbertTmul ψ ψ)
  have hi : (schrodingerTensorRotation m (Real.pi/4)).symm (hilbertTmul ψ ψ) =
      hilbertTmul ψ ψ := by
    apply (schrodingerTensorRotation m (Real.pi/4)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, hf]
  intro r s
  have h := pureTensorCharacteristic_balanced_product m ψ ψ r s
  rw [hi, pureTensorCharacteristic_tmul] at h
  exact h.trans (mul_comm _ _)

/-- The manuscript's positivity and polarization conclusion for any unit
wavefunction accepted by the physical closed-kernel test. -/
theorem pureWaveCharacteristic_kernel_eq_exp_quadratic {m : ℕ} {ψ : WaveSpace m}
    (hn : ‖ψ‖ = 1)
    (hψ : schrodingerTensorP0 m (hilbertTmul ψ ψ) = hilbertTmul ψ ψ) :
    ∃ Q : QuadraticForm ℝ (WavePhase m), Continuous Q ∧
      (∀ r, Q r ≤ 0) ∧
      (∀ r, pureWaveCharacteristic m ψ r = (Real.exp (Q r) : ℂ)) := by
  apply characteristic_rotation_eq_exp_nonpos_quadratic
    (continuous_pureWaveCharacteristic m ψ)
  · simp [hn]
  · exact pureWaveCharacteristic_neg m ψ
  · intro r
    simpa only [hn, one_pow] using norm_pureWaveCharacteristic_le m ψ r
  · exact pureWaveCharacteristic_balanced_of_kernel hψ

end
end GaussianTesting
