module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PhysicalMeanZero
public import GaussianTesting.Bosons.PhysicalCoherent

@[expose] public section

/-!
# The Gaussian forward implication in Proposition 6.3

The manuscript displaces a centered Gaussian state before the balanced
splitter. The inverse splitter moves the identical displacements entirely
to its first output, leaving the centered Gaussian on its second output.
The four-copy projection therefore accepts by Proposition 6.1.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

attribute [local irreducible] schrodingerTensorRotation schrodingerTensorP0
  weylOperator waveVacuum tensorWeylOperator hilbertTmul
  fourCopyInput fourCopyProjection fourCopyPreparation fourCopyAcceptance schrodingerFourCopyAcceptance
  hilbertReshuffle hilbertTensorMap

/-- Identical centered Gaussian states are fixed by every copy rotation,
as used in the Gaussian forward implication of Proposition 6.3. -/
theorem schrodingerTensorRotation_meanZeroGaussian {m : ℕ} {φ : WaveSpace m}
    (hφ : φ ∈ meanZeroGaussianWaveStates m) (θ : ℝ) :
    schrodingerTensorRotation m θ (hilbertTmul φ φ) = hilbertTmul φ φ := by
  obtain ⟨S,hS,z,_,rfl⟩ := hφ
  have h := waveSymplecticUnitary_commutesWithCopyRotations S hS θ
    (hilbertTmul (waveVacuum m) (waveVacuum m))
  simp only [diagonalWaveAction_tmul, schrodingerTensorRotation_vacuum] at h
  simpa only [map_smul, _root_.smul_apply] using
    congrArg (fun v => z • (z • v)) h

/-- The inverse balanced splitter sends identical displaced centered
Gaussians to a product with the original centered Gaussian in register two. -/
theorem displaced_meanZeroGaussian_factorization {m : ℕ} (a : WavePhase m)
    {φ : WaveSpace m} (hφ : φ ∈ meanZeroGaussianWaveStates m) :
    (schrodingerTensorRotation m (Real.pi / 4)).symm
        (hilbertTmul (weylOperator m a φ) (weylOperator m a φ)) =
      hilbertTmul (weylOperator m (Real.sqrt 2 • a) φ) φ := by
  have hinv : (schrodingerTensorRotation m (Real.pi / 4)).symm
      (hilbertTmul φ φ) = hilbertTmul φ φ := by
    apply (schrodingerTensorRotation m (Real.pi / 4)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, schrodingerTensorRotation_meanZeroGaussian hφ]
  apply (schrodingerTensorRotation m (Real.pi / 4)).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  have h := schrodingerTensorRotation_balanced_weyl m (Real.sqrt 2 • a) 0
    (hilbertTmul φ φ)
  simpa only [hinv, tensorWeylOperator_tmul, weylOperator_zero, sub_zero, add_zero,
    smul_smul, inv_mul_cancel₀ (by positivity : Real.sqrt 2 ≠ 0), one_smul] using h.symm

/-- The product output used in the forward Gaussian argument of Proposition 6.3. -/
theorem gaussian_factorization_of_mem_gaussianWaveStates {m : ℕ}
    {ψ : WaveSpace m} (hψ : ψ ∈ gaussianWaveStates m) :
    ∃ u φ : WaveSpace m, ‖u‖ = 1 ∧ φ ∈ meanZeroGaussianWaveStates m ∧
      (schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ) =
        hilbertTmul u φ := by
  obtain ⟨a,S,hS,z,hz,rfl⟩ := hψ
  let φ := z • waveSymplecticUnitary S hS (waveVacuum m)
  have hφ : φ ∈ meanZeroGaussianWaveStates m := ⟨S,hS,z,hz,rfl⟩
  refine ⟨weylOperator m (Real.sqrt 2 • a) φ, φ, ?_, hφ, ?_⟩
  · rw [weylOperator_norm]
    exact norm_eq_one_of_mem_meanZeroGaussianWaveStates hφ
  · simpa only [φ, map_smul] using displaced_meanZeroGaussian_factorization a hφ

/-- Every member of the manuscript's independent Gaussian class is accepted
with certainty by the actual four-copy projection. -/
theorem schrodingerFourCopyAcceptance_of_mem_gaussianWaveStates {m : ℕ}
    {ψ : WaveSpace m} (hψ : ψ ∈ gaussianWaveStates m) :
    schrodingerFourCopyAcceptance ψ = 1 := by
  obtain ⟨u,φ,hu,hφ,hfactor⟩ := gaussian_factorization_of_mem_gaussianWaveStates hψ
  have hφnorm := norm_eq_one_of_mem_meanZeroGaussianWaveStates hφ
  have hfix := (schrodingerTensorP0_fixed_iff_meanZeroGaussianWaveStates φ hφnorm).mpr hφ
  simp only [schrodingerFourCopyAcceptance, fourCopyAcceptance, fourCopyProjection_expectation,
    fourCopyPreparation_input, hfactor, hilbertReshuffle_tmul,
    hilbertTensorMap_tmul, ContinuousLinearMap.id_apply, hfix,
    inner_self_eq_norm_sq_to_K]
  simp only [HilbertDensity.norm_hilbertTmul, hu, hφnorm, one_mul, one_pow,
    RCLike.ofReal_one, Complex.one_re]

end
end GaussianTesting
