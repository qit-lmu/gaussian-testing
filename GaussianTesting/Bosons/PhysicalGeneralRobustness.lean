module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PhysicalGeneralDensity
public import GaussianTesting.Bosons.GaussianSymplecticReduction
public import GaussianTesting.Bosons.PhysicalCoherentRobustness
public import GaussianTesting.Bosons.PhysicalMeanZeroRobustness

@[expose] public section

/-!
# General Gaussian fidelity: Theorem 6.7

The manuscript first extracts the top eigenstate of the reduced density,
uses the mean-zero Gaussian bound, and transports the resulting centered
Gaussian to the vacuum. Commutation with the balanced splitter turns its
reduced-state weight into coherent-test acceptance. The coherent fidelity
bound and inverse symplectic transport finish the argument with constant 48.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

private theorem reducedRight_diagonal_expectation
    {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis κ ℂ E) (V : E ≃ₗᵢ[ℂ] E) (Ψ : HilbertSquare E) (v : E) :
    inner ℂ (V v) (HilbertDensity.reducedRight b b (hilbertTensorEquiv V V Ψ) (V v)) =
      inner ℂ v (HilbertDensity.reducedRight b b Ψ v) := by
  let W := hilbertTensorEquiv V V
  let P := hilbertTensorMap (ContinuousLinearMap.id ℂ E) (InnerProductSpace.rankOne ℂ v v)
  let Q := hilbertTensorMap (ContinuousLinearMap.id ℂ E)
    (InnerProductSpace.rankOne ℂ (V v) (V v))
  have hi : Q.comp W.toContinuousLinearEquiv.toContinuousLinearMap =
      W.toContinuousLinearEquiv.toContinuousLinearMap.comp P := by
    apply hilbertTensor_ext
    intro x y
    simp only [Q, P, W, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      hilbertTensorEquiv_tmul, hilbertTensorMap_tmul, ContinuousLinearMap.id_apply,
      InnerProductSpace.rankOne_apply, map_smul, V.inner_map_map]
  rw [← HilbertDensity.operatorTrace_rankOne_mul b _ (V v) (V v),
    ← HilbertDensity.operatorTrace_rankOne_mul b _ v v,
    HilbertDensity.operatorTrace_mul_reducedRight, HilbertDensity.operatorTrace_mul_reducedRight]
  change inner ℂ (W Ψ) (Q (W Ψ)) = inner ℂ Ψ (P Ψ)
  have hiv : Q (W Ψ) = W (P Ψ) := DFunLike.congr_fun hi Ψ
  rw [hiv, W.inner_map_map]

/-- Commuting Gaussian transport conjugates the reduced-state matrix
coefficient, which is the covariance identity used in Theorem 6.7. -/
theorem schrodingerReducedState_diagonal_expectation {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (V : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (hV : CommutesWithCopyRotations V)
    (ψ v : WaveSpace m) :
    inner ℂ (V v) (schrodingerReducedState b (V ψ) (V v)) =
      inner ℂ v (schrodingerReducedState b ψ v) := by
  have hprep : (schrodingerTensorRotation m (Real.pi / 4)).symm
      (hilbertTmul (V ψ) (V ψ)) =
      hilbertTensorEquiv V V
        ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ)) := by
    simpa only [diagonalWaveAction_eq_tensorEquiv, hilbertTensorEquiv_tmul] using
      hV.inverse_tensorRotation (Real.pi / 4) (hilbertTmul ψ ψ)
  unfold schrodingerReducedState
  rw [hprep]
  exact reducedRight_diagonal_expectation b V _ v

/-- The reduced-operator covariance in the proof of Theorem 6.7:
`σ = V ρ V†` whenever the identical-copy action of `V` commutes with the
physical copy rotations. Equality of the diagonal matrix coefficients gives
the operator identity by complex polarization. -/
theorem schrodingerReducedState_covariance {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (V : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (hV : CommutesWithCopyRotations V)
    (ψ : WaveSpace m) :
    schrodingerReducedState b (V ψ) =
      V.conjStarAlgEquiv (schrodingerReducedState b ψ) := by
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map _ _).mp
  intro x
  obtain ⟨v, rfl⟩ := V.surjective x
  have h := congrArg (starRingEnd ℂ)
    (schrodingerReducedState_diagonal_expectation b V hV ψ v)
  simpa only [ContinuousLinearMap.coe_coe,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, V.inner_map_map, inner_conj_symm] using h

/-- After sending a centered Gaussian to the vacuum, its reduced-state
weight is the acceptance probability of the physical coherent test. -/
theorem schrodingerCoherentAcceptance_inverse_symplectic {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (ψ : WaveSpace m) :
    schrodingerCoherentAcceptance ((waveSymplecticUnitary S hS).symm ψ) =
      (inner ℂ (waveSymplecticUnitary S hS (waveVacuum m))
        (schrodingerReducedState b ψ (waveSymplecticUnitary S hS (waveVacuum m)))).re := by
  rw [schrodingerCoherentAcceptance_eq_vacuumExpectation b,
    schrodingerReducedState_covariance b _
      (waveSymplecticUnitary_commutesWithCopyRotations S hS).symm]
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  have h := (waveSymplecticUnitary S hS).symm.inner_map_map
    (waveSymplecticUnitary S hS (waveVacuum m))
    (schrodingerReducedState b ψ (waveSymplecticUnitary S hS (waveVacuum m)))
  simpa only [LinearIsometryEquiv.symm_apply_apply] using congrArg Complex.re h

/-- A symplectic image of a coherent state is a general Gaussian state,
by the Weyl covariance formula used at the end of Theorem 6.7. -/
theorem symplectic_coherent_mem_gaussianWaveStates {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) {c : WaveSpace m}
    (hc : c ∈ coherentWaveStates m) :
    waveSymplecticUnitary S hS c ∈ gaussianWaveStates m := by
  obtain ⟨a, z, hz, rfl⟩ := hc
  refine ⟨phaseMatrixAction S a, S, hS, z, hz, ?_⟩
  rw [map_smul, waveSymplecticUnitary_weyl]

private theorem expectation_unit_phase {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (ρ : E →L[ℂ] E) (v : E) {z : ℂ} (hz : ‖z‖ = 1) :
    inner ℂ (z • v) (ρ (z • v)) = inner ℂ v (ρ v) := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', hz]
  norm_num

/-- The last half of Theorem 6.7: a centered Gaussian carrying reduced-state
weight `1 - 12τ` produces a general Gaussian witness with overlap `1 - 48τ`.
The first half of the proof supplies the weight by the density reduction. -/
theorem schrodinger_general_fidelity_witness_of_reduced_weight {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1)
    {τ : ℝ} {φ₀ : WaveSpace m} (hφ₀ : φ₀ ∈ meanZeroGaussianWaveStates m)
    (hweight : 1 - 12 * τ ≤ (inner ℂ φ₀ (schrodingerReducedState b ψ φ₀)).re) :
    ∃ φ ∈ gaussianWaveStates m, 1 - 48 * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 ∧
      ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity (gaussianWaveStates m) ψ ^ 2 := by
  obtain ⟨S, hS, z, hz, rfl⟩ := hφ₀
  rw [expectation_unit_phase _ _ hz] at hweight
  let V := waveSymplecticUnitary S hS
  have hq : 1 - 12 * τ ≤ schrodingerCoherentAcceptance (V.symm ψ) := by
    rw [schrodingerCoherentAcceptance_inverse_symplectic b]
    exact hweight
  obtain ⟨c, hc, hlin, _⟩ := schrodinger_coherent_fidelity_witness
    (V.symm ψ) ((V.symm.norm_map ψ).trans hψ) hq
  have hG : V c ∈ gaussianWaveStates m := symplectic_coherent_mem_gaussianWaveStates S hS hc
  refine ⟨V c, hG, ?_, sq_overlap_le_pureFidelity_sq
    (fun _ h => norm_eq_one_of_mem_gaussianWaveStates h) hG⟩
  have hi : inner ℂ (V.symm ψ) c = inner ℂ ψ (V c) := by
    simpa only [V.apply_symm_apply] using (V.inner_map_map (V.symm ψ) c).symm
  rw [hi] at hlin
  linarith

/-- **Theorem 6.7**, with a physical Gaussian witness. The proof extracts the
top reduced eigenstate, applies the mean-zero bound, and then uses the
manuscript's symplectic reduction to the coherent bound. -/
theorem schrodinger_gaussian_fidelity_witness {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerFourCopyAcceptance ψ) :
    ∃ φ ∈ gaussianWaveStates m, 1 - 48 * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 ∧
      ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity (gaussianWaveStates m) ψ ^ 2 := by
  let b : HilbertBasis (Fin m → ℕ) ℂ (WaveSpace m) :=
    .ofRepr (fockSchrodingerEquiv m).symm
  let c : HilbertBasis ((Fin m → ℕ) × (Fin m → ℕ)) ℂ (SchrodingerSpace m) :=
    .ofRepr ((waveTensorEquiv m).symm.trans (HilbertDensity.tensorBasis b).repr)
  have hτ0 : 0 ≤ τ := by
    have hprob := (schrodingerFourCopyAcceptance_mem_Icc b c ψ hψ).2
    linarith
  by_cases hsmall : τ ≤ 1 / 48
  · obtain ⟨ξ, hξ, heig, hlower, _, hacc, _⟩ :=
      schrodingerReducedState_top_eigenstate b c hψ hsmall hp
    obtain ⟨φ₀, hφ₀, ho, _⟩ := schrodinger_meanZero_fidelity_witness ξ hξ hacc
    have hρ := schrodingerReducedState_isDensityOperator b ψ hψ
    exact schrodinger_general_fidelity_witness_of_reduced_weight b ψ hψ hφ₀
      (hρ.eigenstate_weight_ge_of_overlap hξ heig hτ0 hsmall hlower ho)
  · have hvac : waveVacuum m ∈ coherentWaveStates m := by
      refine ⟨0, 1, norm_one, ?_⟩
      simp only [weylOperator_zero, one_smul]
    let S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ := 1
    have hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ := (Matrix.symplecticGroup (Fin m) ℝ).one_mem
    let φ := waveSymplecticUnitary S hS (waveVacuum m)
    have hφ : φ ∈ gaussianWaveStates m := symplectic_coherent_mem_gaussianWaveStates S hS hvac
    refine ⟨φ, hφ, ?_, sq_overlap_le_pureFidelity_sq
      (fun _ h => norm_eq_one_of_mem_gaussianWaveStates h) hφ⟩
    nlinarith [sq_nonneg ‖inner ℂ ψ φ‖]

/-- **Theorem 6.7.** Acceptance at least `1 - τ` by the actual four-copy
test implies squared fidelity at least `1 - 48τ` with general Gaussian states. -/
theorem schrodinger_gaussian_fidelity {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerFourCopyAcceptance ψ) :
    1 - 48 * τ ≤ pureFidelity (gaussianWaveStates m) ψ ^ 2 := by
  obtain ⟨_, _, hlin, hfid⟩ := schrodinger_gaussian_fidelity_witness ψ hψ hp
  exact hlin.trans hfid

end
end GaussianTesting
