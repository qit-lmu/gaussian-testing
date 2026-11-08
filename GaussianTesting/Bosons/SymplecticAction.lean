module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GaussianUnitaryGenerators
public import GaussianTesting.Bosons.PhaseSpaceMatrix
public import GaussianTesting.Bosons.SymplecticDecomposition

@[expose] public section

/-!
# Symplectic Gaussian unitaries on the Schrödinger space

Every real symplectic matrix has a physical unitary implementation on Lebesgue
`L²`, with the manuscript's Weyl covariance and exact commutation of identical
copies with copy rotations. The construction uses quadratic phases, normalized
linear position changes, and the Fourier transform.

The phase coordinates are `(q,p)`. Mathlib defines its symplectic group using
`(0,-I;I,0)`, the negative of the manuscript's `Ω`; this defines the same group.
Only existence and the covariance needed by Section 6 are asserted here.
-/

namespace GaussianTesting

open Matrix

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true

/-- A physical unitary implementing a phase-space matrix, whose identical
copies commute with the manuscript's copy rotations. -/
def HasWaveImplementation {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) : Prop :=
  ∃ U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m,
    WeylIntertwines U (phaseMatrixAction S) ∧ CommutesWithCopyRotations U

theorem HasWaveImplementation.mul {m : ℕ}
    {S T : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ}
    (hS : HasWaveImplementation S) (hT : HasWaveImplementation T) :
    HasWaveImplementation (S*T) := by
  obtain ⟨U, hU, hUr⟩ := hS
  obtain ⟨V, hV, hVr⟩ := hT
  refine ⟨V.trans U, ?_, hVr.trans hUr⟩
  intro r f
  simpa only [Function.comp_apply, ← phaseMatrixAction_mul] using (hV.trans hU) r f

private theorem waveMatrixCLM_one_apply {m : ℕ} (x : WaveConfig m) :
    waveMatrixCLM 1 x = x := by
  ext i
  simp [waveMatrixCLM_apply]

private theorem waveMatrixCLM_zero_apply {m : ℕ} (x : WaveConfig m) :
    waveMatrixCLM 0 x = 0 := by
  ext i
  simp [waveMatrixCLM_apply]

/-- Symmetric lower shears are implemented by quadratic phase multipliers. -/
theorem hasWaveImplementation_lowerShear {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    HasWaveImplementation (fromBlocks 1 0 A 1) := by
  refine ⟨waveQuadraticPhase m (waveMatrixCLM A), ?_,
    quadraticPhase_commutesWithCopyRotations m _⟩
  intro r f
  simpa only [phaseMatrixAction_fromBlocks, waveMatrixCLM_one_apply,
    waveMatrixCLM_zero_apply, add_zero, add_comm] using
    weylIntertwines_quadraticPhase m _ (waveMatrixCLM_symmetric hA) r f

/-- Symmetric upper shears are implemented by Fourier-conjugated quadratic phases. -/
theorem hasWaveImplementation_upperShear {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    HasWaveImplementation (fromBlocks 1 A 0 1) := by
  refine ⟨waveUpperShear m (waveMatrixCLM A), ?_,
    upperShear_commutesWithCopyRotations m _⟩
  intro r f
  simpa only [phaseMatrixAction_fromBlocks, waveMatrixCLM_one_apply,
    waveMatrixCLM_zero_apply, zero_add] using
    weylIntertwines_upperShear m _ (waveMatrixCLM_symmetric hA) r f

/-- Invertible coordinate changes implement the block-diagonal symplectic maps. -/
theorem hasWaveImplementation_diagonal {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : IsUnit A) :
    HasWaveImplementation (fromBlocks A 0 0 A⁻¹ᵀ) := by
  refine ⟨(waveLinearChange m (waveMatrixEquiv A hA)).symm, ?_,
    (linearChange_commutesWithCopyRotations m _).symm⟩
  have he : (waveMatrixEquiv A hA).symm.toContinuousLinearMap = waveMatrixCLM A⁻¹ := by
    ext1 x
    exact waveMatrixEquiv_symm_apply A hA x
  intro r f
  simpa only [waveLinearChangePhase, phaseMatrixAction_fromBlocks,
    waveMatrixCLM_zero_apply, add_zero, zero_add, waveMatrixEquiv_apply,
    waveMatrixCLM_transpose, he] using
    weylIntertwines_linearChange_symm m (waveMatrixEquiv A hA) r f

/-- Every real symplectic matrix has a physical Gaussian-unitary implementation.
This is an existence theorem on the actual Schrödinger Hilbert space. -/
theorem symplectic_hasWaveImplementation {m : ℕ}
    {S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ}
    (hS : S ∈ symplecticGroup (Fin m) ℝ) : HasWaveImplementation S := by
  obtain ⟨X, Y, Z, A, hX, hY, hZ, hA, rfl⟩ := symplectic_decomposition hS
  exact (((hasWaveImplementation_upperShear X hX).mul
    (hasWaveImplementation_lowerShear Y hY)).mul
    (hasWaveImplementation_diagonal A hA)).mul
    (hasWaveImplementation_upperShear Z hZ)

/-- A choice of the manuscript's `U_S` for each symplectic matrix `S`. -/
def waveSymplecticUnitary {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ symplecticGroup (Fin m) ℝ) : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m :=
  (symplectic_hasWaveImplementation hS).choose

/-- Forward covariance, equivalent to the manuscript's inverse conjugation formula. -/
theorem waveSymplecticUnitary_weyl {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ symplecticGroup (Fin m) ℝ) (r : WavePhase m) (f : WaveSpace m) :
    waveSymplecticUnitary S hS (weylOperator m r f) =
      weylOperator m (phaseMatrixAction S r) (waveSymplecticUnitary S hS f) :=
  (symplectic_hasWaveImplementation hS).choose_spec.1 r f

/-- The Section 6 Weyl covariance `U_S† D_r U_S = D_(S⁻¹r)`. -/
theorem waveSymplecticUnitary_conjugate_weyl {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ symplecticGroup (Fin m) ℝ) (r : WavePhase m) (f : WaveSpace m) :
    (waveSymplecticUnitary S hS).symm (weylOperator m r (waveSymplecticUnitary S hS f)) =
      weylOperator m (phaseMatrixAction S⁻¹ r) f := by
  have hunit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr
    (SymplecticGroup.symplectic_det hS)
  let : Invertible S := hunit.invertible
  have hp : phaseMatrixAction S (phaseMatrixAction S⁻¹ r) = r := by
    rw [← phaseMatrixAction_mul, Matrix.mul_inv_of_invertible, phaseMatrixAction_one]
  apply (waveSymplecticUnitary S hS).injective
  rw [LinearIsometryEquiv.apply_symm_apply, waveSymplecticUnitary_weyl, hp]

/-- Identical symplectic Gaussian unitaries commute exactly with every copy rotation. -/
theorem waveSymplecticUnitary_commutesWithCopyRotations {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ symplecticGroup (Fin m) ℝ) :
    CommutesWithCopyRotations (waveSymplecticUnitary S hS) :=
  (symplectic_hasWaveImplementation hS).choose_spec.2

/-- Symplectic covariance of the characteristic function of a pure state. -/
theorem pureWaveCharacteristic_symplectic {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ symplecticGroup (Fin m) ℝ) (r : WavePhase m) (f : WaveSpace m) :
    pureWaveCharacteristic m (waveSymplecticUnitary S hS f) r =
      pureWaveCharacteristic m f (phaseMatrixAction S⁻¹ r) := by
  unfold pureWaveCharacteristic
  rw [(waveSymplecticUnitary S hS).inner_map_eq_flip,
    waveSymplecticUnitary_conjugate_weyl]

end
end GaussianTesting
