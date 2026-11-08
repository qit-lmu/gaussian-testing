module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PhysicalCoherent
public import GaussianTesting.Bosons.GaussianKernel
public import GaussianTesting.Bosons.GaussianWaveStates

@[expose] public section

/-!
# The symplectic reduction in Proposition 6.3

When the inverse splitter has a centered Gaussian right factor, apply the
inverse Gaussian unitary on both copies to turn it into the vacuum. Copy
rotation commutation reduces the input to the coherent test. Weyl covariance
then transports the displaced vacuum back to a general Gaussian state.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

attribute [local irreducible] schrodingerTensorRotation schrodingerQ waveVacuum
  weylOperator hilbertTmul waveSymplecticUnitary

/-- The inverse splitter also commutes with identical Gaussian actions. -/
theorem CommutesWithCopyRotations.inverse_tensorRotation {m : ℕ}
    {V : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m} (hV : CommutesWithCopyRotations V)
    (θ : ℝ) (w : HilbertSquare (WaveSpace m)) :
    (schrodingerTensorRotation m θ).symm (diagonalWaveAction V w) =
      diagonalWaveAction V ((schrodingerTensorRotation m θ).symm w) := by
  apply (schrodingerTensorRotation m θ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, hV,
    LinearIsometryEquiv.apply_symm_apply]

/-- A vacuum factor in the inverse splitter output is accepted by the coherent
test; this is the reduction used in Proposition 6.3. -/
theorem coherent_acceptance_one_of_vacuum_factorization {m : ℕ}
    (ψ u : WaveSpace m) (hψ : ‖ψ‖ = 1)
    (hfactor : (schrodingerTensorRotation m (Real.pi / 4)).symm
      (hilbertTmul ψ ψ) = hilbertTmul u (waveVacuum m)) :
    schrodingerCoherentAcceptance ψ = 1 := by
  apply (schrodingerCoherentAcceptance_eq_one_iff_fixed ψ hψ).mpr
  simp only [schrodingerQ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    hfactor, hilbertTensorMap_tmul, ContinuousLinearMap.id_apply,
    waveVacuumProjection_apply, inner_self_eq_norm_sq_to_K, waveVacuum_norm,
    RCLike.ofReal_one, one_pow, one_smul]
  exact (congrArg (schrodingerTensorRotation m (Real.pi / 4)) hfactor.symm).trans
    ((schrodingerTensorRotation m (Real.pi / 4)).apply_symm_apply _)

/-- The manuscript's reduction of a pure centered Gaussian output to coherent
certainty, followed by symplectic transport back to the Gaussian input class. -/
theorem mem_gaussianWaveStates_of_meanZero_factorization {m : ℕ}
    (ψ u φ : WaveSpace m) (hψ : ‖ψ‖ = 1)
    (hφ : φ ∈ meanZeroGaussianWaveStates m)
    (hfactor : (schrodingerTensorRotation m (Real.pi / 4)).symm
      (hilbertTmul ψ ψ) = hilbertTmul u φ) :
    ψ ∈ gaussianWaveStates m := by
  obtain ⟨S, hS, z, _, rfl⟩ := hφ
  let V := waveSymplecticUnitary S hS
  have hV := (waveSymplecticUnitary_commutesWithCopyRotations S hS).symm
  have hnew : (schrodingerTensorRotation m (Real.pi / 4)).symm
      (hilbertTmul (V.symm ψ) (V.symm ψ)) =
      hilbertTmul (z • V.symm u) (waveVacuum m) := by
    have h := hV.inverse_tensorRotation (Real.pi / 4) (hilbertTmul ψ ψ)
    rw [hfactor] at h
    simpa only [diagonalWaveAction_eq_tensorEquiv, hilbertTensorEquiv_tmul,
      map_smul, LinearIsometryEquiv.symm_apply_apply, V, smul_apply] using h
  have hn : ‖V.symm ψ‖ = 1 := (V.symm.norm_map ψ).trans hψ
  have hacc := coherent_acceptance_one_of_vacuum_factorization
    (V.symm ψ) (z • V.symm u) hn hnew
  obtain ⟨a, c, hc, he⟩ := (schrodingerCoherentAcceptance_eq_one_iff _ hn).mp hacc
  refine ⟨phaseMatrixAction S a, S, hS, c, hc, ?_⟩
  have h := congrArg V he
  simpa only [LinearIsometryEquiv.apply_symm_apply, map_smul, V,
    waveSymplecticUnitary_weyl] using h

end
end GaussianTesting
