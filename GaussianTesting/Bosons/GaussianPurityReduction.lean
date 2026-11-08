module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PhysicalMeanZero
public import GaussianTesting.Bosons.DensityPure
public import GaussianTesting.Bosons.PureFactorization

@[expose] public section

/-!
# The purity reduction in Proposition 6.3

Perfect four-copy acceptance forces the reduced state after the inverse
balanced rotation to have norm one, by Lemma 6.2. It is therefore pure.
The resulting product factorization and Proposition 6.1 identify its second
factor as a centered Gaussian. These are steps of Proposition 6.3's proof.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] schrodingerTensorRotation schrodingerTensorP0 hilbertTmul
  schrodingerMeanZeroAcceptance schrodingerFourCopyAcceptance schrodingerReducedState
  meanZeroGaussianWaveStates

/-- When the inverse splitter output is a product with a unit first factor,
the four-copy probability is exactly the centered test probability of the
second factor. -/
theorem schrodingerFourCopyAcceptance_of_factorization {m : ℕ}
    (ψ u φ : WaveSpace m) (hu : ‖u‖ = 1)
    (hfactor : (schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ) =
      hilbertTmul u φ) :
    schrodingerFourCopyAcceptance ψ = schrodingerMeanZeroAcceptance φ := by
  unfold schrodingerFourCopyAcceptance fourCopyAcceptance
  simp only [fourCopyProjection_expectation, fourCopyPreparation_input, hfactor,
    hilbertReshuffle_tmul, hilbertTensorMap_tmul, ContinuousLinearMap.id_apply,
    inner_hilbertTmul, inner_self_eq_norm_sq_to_K, HilbertDensity.norm_hilbertTmul, hu,
    RCLike.ofReal_one, one_pow, one_mul]
  unfold schrodingerMeanZeroAcceptance TensorSquare.accProbA
  rfl

private theorem density_norm_le_one {E κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {b : HilbertBasis κ ℂ E} {ρ : E →L[ℂ] E}
    (hρ : HilbertDensity.IsDensityOperator b ρ) : ‖ρ‖ ≤ 1 := by
  obtain ⟨g, hg, hmass, rfl⟩ := hρ.exists_normalized_gram_representation
  have h := gramOp_norm_le (hg.inBasis b)
  rw [← HilbertDensity.inBasis_gramOp b g hg, HilbertDensity.inBasis_norm] at h
  simpa only [b.repr.norm_map, hmass] using h

/-- In Proposition 6.3, perfect four-copy acceptance forces the actual
reduced density operator to be a pure state. The basis only defines the trace. -/
theorem schrodingerReducedState_rankOne_of_acceptance_one {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m)
    (hψ : ‖ψ‖ = 1) (hp : schrodingerFourCopyAcceptance ψ = 1) :
    ∃ φ : WaveSpace m, ‖φ‖ = 1 ∧
      schrodingerReducedState b ψ = InnerProductSpace.rankOne ℂ φ φ := by
  obtain ⟨s, c, _⟩ := exists_hilbertBasis ℂ (SchrodingerSpace m)
  have hρ := schrodingerReducedState_isDensityOperator b ψ hψ
  have hp' := (schrodingerFourCopyAcceptance_eq_reducedTrace b c ψ).symm.trans hp
  rw [schrodingerDensityTensor,
    (hρ.embeddedTensor c (waveTensor m)).toIsPositiveTraceClass.operatorTrace_mul_comm]
    at hp'
  have hl : 1 ≤ ‖schrodingerReducedState b ψ‖ := by
    simpa only [mul_zero, sub_zero] using
      (purity_schrodinger c hρ (τ := 0) (by simpa only [sub_zero, schrodingerDensityTensor] using le_of_eq hp'.symm))
  exact hρ.exists_rankOne_of_norm_eq_one (le_antisymm (density_norm_le_one hρ) hl)

/-- The first part of Proposition 6.3's Gaussian converse: the inverse
splitter output has a unit first factor and a centered Gaussian second factor.
This follows the manuscript's reduced-state purity argument. -/
theorem gaussian_factorization_of_fourCopyAcceptance_one {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) (hp : schrodingerFourCopyAcceptance ψ = 1) :
    ∃ u φ : WaveSpace m, ‖u‖ = 1 ∧ φ ∈ meanZeroGaussianWaveStates m ∧
      (schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ) =
        hilbertTmul u φ := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ (WaveSpace m)
  have hpure : ∃ φ : WaveSpace m, ‖φ‖ = 1 ∧
      schrodingerReducedState b ψ = InnerProductSpace.rankOne ℂ φ φ :=
    schrodingerReducedState_rankOne_of_acceptance_one (m := m) (κ := s) b ψ hψ hp
  obtain ⟨φ, hφ, hρ⟩ := hpure
  have hout : ‖(schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, HilbertDensity.norm_hilbertTmul, hψ, one_mul]
  have hρ' : HilbertDensity.reducedRight b b
      ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) =
      InnerProductSpace.rankOne ℂ φ φ := by
    simpa only [schrodingerReducedState] using hρ
  have hproduct : ∃ u : WaveSpace m, ‖u‖ = 1 ∧
      (schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ) =
        hilbertTmul u φ :=
    HilbertDensity.exists_unit_tmul_of_reducedRight_eq_rankOne
      (E := WaveSpace m) (F := WaveSpace m) (ι := s) (κ := s)
      b b ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ))
      hout φ hφ hρ'
  obtain ⟨u, hu, hf⟩ := hproduct
  refine ⟨u, φ, hu, ?_, hf⟩
  apply (schrodingerMeanZeroAcceptance_eq_one_iff (m := m) φ hφ).mp
  exact (schrodingerFourCopyAcceptance_of_factorization (m := m) ψ u φ hu hf).symm.trans hp

end
end GaussianTesting
