module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.FourierTensor
public import GaussianTesting.Bosons.SymplecticShear

@[expose] public section

/-!
# Physical generators for symplectic Gaussian unitaries

Quadratic phase multipliers, Jacobian-normalized position changes, and Fourier
transforms act on the actual Schrödinger space. Each intertwines Weyl operators
by its stated phase-space transformation, and its identical action on two copies
commutes with copy rotations. These properties are preserved by composition.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true

/-- Apply the same one-copy unitary to both completed tensor factors. -/
def diagonalWaveAction {m : ℕ} (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) :
    HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) :=
  hilbertTensorMap U.toLinearIsometry.toContinuousLinearMap
    U.toLinearIsometry.toContinuousLinearMap

@[simp] theorem diagonalWaveAction_tmul {m : ℕ}
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (f g : WaveSpace m) :
    diagonalWaveAction U (hilbertTmul f g) = hilbertTmul (U f) (U g) :=
  hilbertTensorMap_tmul _ _ _ _

theorem diagonalWaveAction_trans {m : ℕ} (U V : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m)
    (v : HilbertSquare (WaveSpace m)) :
    diagonalWaveAction (U.trans V) v = diagonalWaveAction V (diagonalWaveAction U v) := by
  have h : diagonalWaveAction (U.trans V) = (diagonalWaveAction V).comp (diagonalWaveAction U) := by
    apply hilbertTensor_ext
    intro f g
    simp only [diagonalWaveAction_tmul, ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.trans_apply]
  exact congrArg (fun A => A v) h

@[simp] theorem diagonalWaveAction_symm_left {m : ℕ}
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (v : HilbertSquare (WaveSpace m)) :
    diagonalWaveAction U.symm (diagonalWaveAction U v) = v := by
  have h : (diagonalWaveAction U.symm).comp (diagonalWaveAction U) =
      ContinuousLinearMap.id ℂ (HilbertSquare (WaveSpace m)) := by
    apply hilbertTensor_ext
    intro f g
    simp only [ContinuousLinearMap.comp_apply, diagonalWaveAction_tmul,
      LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]
  exact congrArg (fun A => A v) h

@[simp] theorem diagonalWaveAction_symm_right {m : ℕ}
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (v : HilbertSquare (WaveSpace m)) :
    diagonalWaveAction U (diagonalWaveAction U.symm v) = v :=
  diagonalWaveAction_symm_left U.symm v

/-- Forward Weyl covariance under a specified phase-space map. -/
def WeylIntertwines {m : ℕ} (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m)
    (T : WavePhase m → WavePhase m) : Prop :=
  ∀ r f, U (weylOperator m r f) = weylOperator m (T r) (U f)

/-- Identical copies of the unitary commute with every coordinate rotation. -/
def CommutesWithCopyRotations {m : ℕ} (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) : Prop :=
  ∀ θ v, schrodingerTensorRotation m θ (diagonalWaveAction U v) =
    diagonalWaveAction U (schrodingerTensorRotation m θ v)

theorem WeylIntertwines.trans {m : ℕ} {U V : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m}
    {T R : WavePhase m → WavePhase m} (hU : WeylIntertwines U T) (hV : WeylIntertwines V R) :
    WeylIntertwines (U.trans V) (R ∘ T) := by
  intro r f
  simp only [LinearIsometryEquiv.trans_apply, hU r f, Function.comp_apply]
  exact hV (T r) (U f)

theorem WeylIntertwines.of_conjugate {m : ℕ}
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (T : WavePhase m → WavePhase m)
    (h : ∀ r f, U.symm (weylOperator m r (U f)) = weylOperator m (T r) f) :
    WeylIntertwines U.symm T := by
  intro r f
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h r (U.symm f)

theorem CommutesWithCopyRotations.trans {m : ℕ}
    {U V : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m}
    (hU : CommutesWithCopyRotations U) (hV : CommutesWithCopyRotations V) :
    CommutesWithCopyRotations (U.trans V) := by
  intro θ v
  rw [diagonalWaveAction_trans, hV, hU, ← diagonalWaveAction_trans]

theorem CommutesWithCopyRotations.symm {m : ℕ}
    {U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m} (hU : CommutesWithCopyRotations U) :
    CommutesWithCopyRotations U.symm := by
  have hinj : Function.Injective (diagonalWaveAction U) :=
    Function.LeftInverse.injective (diagonalWaveAction_symm_left U)
  intro θ v
  apply hinj
  rw [← hU, diagonalWaveAction_symm_right, diagonalWaveAction_symm_right]

/-- Symmetric quadratic phases implement lower symplectic shears. -/
theorem weylIntertwines_quadraticPhase (m : ℕ)
    (A : WaveConfig m →L[ℝ] WaveConfig m) (hA : A.toLinearMap.IsSymmetric) :
    WeylIntertwines (waveQuadraticPhase m A) (fun r => (r.1, r.2 + A r.1)) := by
  have hneg : (-A).toLinearMap.IsSymmetric := by
    intro x y
    simpa only [ContinuousLinearMap.toLinearMap_neg, LinearMap.neg_apply,
      inner_neg_left, inner_neg_right] using congrArg Neg.neg (hA x y)
  have h := WeylIntertwines.of_conjugate (waveQuadraticPhase m (-A))
    (fun r => (r.1, r.2 - (-A) r.1)) (waveQuadraticPhase_weyl m (-A) hneg)
  simpa only [waveQuadraticPhase_symm, neg_neg, neg_apply,
    sub_neg_eq_add] using h

theorem quadraticPhase_commutesWithCopyRotations (m : ℕ)
    (A : WaveConfig m →L[ℝ] WaveConfig m) :
    CommutesWithCopyRotations (waveQuadraticPhase m A) :=
  fun θ v => schrodingerTensorRotation_quadraticPhase m A θ v

/-- The inverse normalized pullback implements the block-diagonal symplectic map. -/
theorem weylIntertwines_linearChange_symm (m : ℕ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    WeylIntertwines (waveLinearChange m A).symm (waveLinearChangePhase A) :=
  WeylIntertwines.of_conjugate _ _ (waveLinearChange_weyl m A)

theorem linearChange_commutesWithCopyRotations (m : ℕ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    CommutesWithCopyRotations (waveLinearChange m A) :=
  fun θ v => schrodingerTensorRotation_linearChange m A θ v

theorem weylIntertwines_fourier (m : ℕ) :
    WeylIntertwines (waveFourier m) waveFourierPhase := waveFourier_weyl m

theorem weylIntertwines_fourier_symm (m : ℕ) :
    WeylIntertwines (waveFourier m).symm
      (fun r => (-(2 * Real.pi)⁻¹ • r.2, (2 * Real.pi) • r.1)) :=
  WeylIntertwines.of_conjugate _ _ (waveFourier_conjugate m)

theorem fourier_commutesWithCopyRotations (m : ℕ) :
    CommutesWithCopyRotations (waveFourier m) :=
  fun θ v => schrodingerTensorRotation_fourier m θ v

/-- Upper shears are Fourier conjugates of quadratic phase multipliers.
The factor `(2π)²` compensates exactly for Mathlib's Fourier normalization. -/
def waveUpperShear (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m) :
    WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m :=
  (waveFourier m).trans ((waveQuadraticPhase m (-((2 * Real.pi)^2) • A)).trans
    (waveFourier m).symm)

theorem weylIntertwines_upperShear (m : ℕ)
    (A : WaveConfig m →L[ℝ] WaveConfig m) (hA : A.toLinearMap.IsSymmetric) :
    WeylIntertwines (waveUpperShear m A) (fun r => (r.1 + A r.2, r.2)) := by
  have hs : (-((2 * Real.pi)^2) • A).toLinearMap.IsSymmetric := by
    intro x y
    simpa only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply,
      real_inner_smul_left, inner_smul_right] using congrArg (fun t => -((2 * Real.pi)^2) * t) (hA x y)
  have h := (weylIntertwines_fourier m).trans
    ((weylIntertwines_quadraticPhase m _ hs).trans (weylIntertwines_fourier_symm m))
  intro r f
  have hp : ((fun r : WavePhase m => (-(2 * Real.pi)⁻¹ • r.2, (2 * Real.pi) • r.1)) ∘
      (fun r : WavePhase m => (r.1, r.2 + (-((2 * Real.pi)^2) • A) r.1)) ∘
      waveFourierPhase) r = (r.1 + A r.2, r.2) := by
    apply Prod.ext <;> ext i
    · simp only [Function.comp_apply, waveFourierPhase, smul_apply,
        map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
    · simp only [Function.comp_apply, waveFourierPhase, PiLp.smul_apply, smul_eq_mul]
      field_simp
  exact (h r f).trans (congrArg (fun t => weylOperator m t (waveUpperShear m A f)) hp)

theorem upperShear_commutesWithCopyRotations (m : ℕ)
    (A : WaveConfig m →L[ℝ] WaveConfig m) :
    CommutesWithCopyRotations (waveUpperShear m A) :=
  (fourier_commutesWithCopyRotations m).trans
    ((quadraticPhase_commutesWithCopyRotations m _).trans
      (fourier_commutesWithCopyRotations m).symm)

end
end GaussianTesting
