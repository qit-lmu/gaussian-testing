module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SymplecticAction
public import GaussianTesting.Bosons.RotationFixedSpace

@[expose] public section

/-!
# Gaussian invariance of the required kernel projection

Identical-copy commutation with the actual rotation group preserves its fixed
subspace, hence the manuscript's closed `Λ` kernel and accepting projection.
These are the invariance facts used by the Section 6 proofs.
-/

namespace GaussianTesting

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The identical one-copy unitary, represented on two-copy wavefunctions. -/
def schrodingerDiagonalAction {m : ℕ} (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) :
    SchrodingerSpace m ≃ₗᵢ[ℂ] SchrodingerSpace m :=
  (waveTensorEquiv m).symm.trans ((hilbertTensorEquiv U U).trans (waveTensorEquiv m))

theorem diagonalWaveAction_eq_tensorEquiv {m : ℕ}
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (v : HilbertSquare (WaveSpace m)) :
    diagonalWaveAction U v = hilbertTensorEquiv U U v := by
  exact (DFunLike.congr_fun (hilbertTensorEquiv_toContinuousLinearMap U U) v).symm

@[simp] theorem schrodingerDiagonalAction_waveTensor {m : ℕ}
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (v : HilbertSquare (WaveSpace m)) :
    schrodingerDiagonalAction U (waveTensorEquiv m v) =
      waveTensorEquiv m (diagonalWaveAction U v) := by
  simp only [schrodingerDiagonalAction, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply, diagonalWaveAction_eq_tensorEquiv]

@[simp] theorem schrodingerDiagonalAction_symm {m : ℕ}
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) :
    (schrodingerDiagonalAction U).symm = schrodingerDiagonalAction U.symm := by
  simp only [schrodingerDiagonalAction, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, hilbertTensorEquiv_symm]
  rfl

/-- Copy-rotation commutation in physical product coordinates. -/
theorem CommutesWithCopyRotations.schrodinger {m : ℕ}
    {U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m} (hU : CommutesWithCopyRotations U)
    (θ : ℝ) (f : SchrodingerSpace m) :
    schrodingerRotation m θ (schrodingerDiagonalAction U f) =
      schrodingerDiagonalAction U (schrodingerRotation m θ f) := by
  obtain ⟨v,rfl⟩ := (waveTensorEquiv m).surjective f
  have h := congrArg (waveTensorEquiv m) (hU θ v)
  simpa only [schrodingerTensorRotation, schrodingerDiagonalAction,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply, diagonalWaveAction_eq_tensorEquiv] using h

/-- The invariant subspace interpretation preserves the prescribed closed kernel. -/
theorem CommutesWithCopyRotations.mem_kernel {m : ℕ}
    {U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m} (hU : CommutesWithCopyRotations U)
    {f : SchrodingerSpace m} (hf : f ∈ (schrodingerLambda m).ker) :
    schrodingerDiagonalAction U f ∈ (schrodingerLambda m).ker := by
  apply (schrodingerLambda_mem_kernel_iff_rotation_fixed m _).mpr
  intro θ
  rw [hU.schrodinger, (schrodingerLambda_mem_kernel_iff_rotation_fixed m f).mp hf θ]

/-- Gaussian covariance of the actual bounded accepting projection, with no
unbounded-domain hypothesis supplied by a caller. -/
theorem CommutesWithCopyRotations.schrodingerP0 {m : ℕ}
    {U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m} (hU : CommutesWithCopyRotations U)
    (f : SchrodingerSpace m) :
    schrodingerDiagonalAction U (schrodingerP0 m f) =
      schrodingerP0 m (schrodingerDiagonalAction U f) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hU.mem_kernel ((schrodingerLambda m).ker.starProjection_apply_mem f)
  · intro w hw
    obtain ⟨v,rfl⟩ := (schrodingerDiagonalAction U).surjective w
    have hv : v ∈ (schrodingerLambda m).ker := by
      have h := hU.symm.mem_kernel hw
      rw [← schrodingerDiagonalAction_symm, LinearIsometryEquiv.symm_apply_apply] at h
      exact h
    rw [← map_sub, (schrodingerDiagonalAction U).inner_map_map]
    exact Submodule.starProjection_inner_eq_zero _ _ hv

/-- The kernel projection commutes with the identical Gaussian action also on
completed tensor coordinates. -/
theorem CommutesWithCopyRotations.tensorP0 {m : ℕ}
    {U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m} (hU : CommutesWithCopyRotations U)
    (v : HilbertSquare (WaveSpace m)) :
    diagonalWaveAction U (schrodingerTensorP0 m v) =
      schrodingerTensorP0 m (diagonalWaveAction U v) := by
  apply (waveTensorEquiv m).injective
  simpa only [schrodingerTensorP0, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    ← schrodingerDiagonalAction_waveTensor] using hU.schrodingerP0 (waveTensorEquiv m v)

/-- The symplectic Gaussian unitaries preserve the physical kernel test. -/
theorem waveSymplecticUnitary_tensorP0 {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ)
    (v : HilbertSquare (WaveSpace m)) :
    diagonalWaveAction (waveSymplecticUnitary S hS) (schrodingerTensorP0 m v) =
      schrodingerTensorP0 m (diagonalWaveAction (waveSymplecticUnitary S hS) v) :=
  (waveSymplecticUnitary_commutesWithCopyRotations S hS).tensorP0 v

/-- Fixing the physical kernel projection is exactly kernel membership. -/
theorem schrodingerTensorP0_fixed_iff (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorP0 m v = v ↔ waveTensorEquiv m v ∈ (schrodingerLambda m).ker := by
  rw [← (waveTensorEquiv m).injective.eq_iff]
  simp only [schrodingerTensorP0, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
  exact Submodule.starProjection_eq_self_iff

end
end GaussianTesting
