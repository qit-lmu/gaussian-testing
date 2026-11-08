module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.CoherentCharacteristic
public import GaussianTesting.Bosons.SchrodingerCoherent
public import GaussianTesting.Bosons.VacuumTensor
public import GaussianTesting.GradientFlow.RankOneTensor

@[expose] public section

/-!
# Physical coherent certainty in Proposition 6.3

Unit acceptance means that the inverse balanced splitter has vacuum in its
second output. The manuscript's characteristic-function argument then
identifies the input pure state with a displaced vacuum.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

attribute [local irreducible] schrodingerQ schrodingerTensorRotation
  weylOperator waveVacuum waveVacuumProjection tensorWeylOperator hilbertTmul
  schrodingerCoherentAcceptance

/-- A fixed vector of `I ⊗ |0⟩⟨0|` has a vacuum factor in its second register. -/
theorem exists_vacuum_factor_of_tensor_projection_fixed (m : ℕ)
    (w : HilbertSquare (WaveSpace m))
    (hw : hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
      (waveVacuumProjection m) w = w) :
    ∃ φ : WaveSpace m, w = hilbertTmul φ (waveVacuum m) := by
  let J : WaveSpace m →L[ℂ] HilbertSquare (WaveSpace m) := hilbertTmul.flip (waveVacuum m)
  rw [waveVacuumProjection, hilbertTensorMap_rankOne_right] at hw
  refine ⟨J.adjoint w, ?_⟩
  exact hw.symm

/-- For a unit input, coherent certainty is equivalent to the projection
fixing the two-copy input. -/
theorem schrodingerCoherentAcceptance_eq_one_iff_fixed {m : ℕ} (ψ : WaveSpace m)
    (hψ : ‖ψ‖ = 1) : schrodingerCoherentAcceptance ψ = 1 ↔
      schrodingerQ m (hilbertTmul ψ ψ) = hilbertTmul ψ ψ := by
  have hn : ‖hilbertTmul ψ ψ‖ = 1 := by
    simpa only [hilbertTensorSquare, hψ, one_mul] using
      (hilbertTensorSquare (WaveSpace m)).norm_tp ψ ψ
  unfold schrodingerCoherentAcceptance TensorSquare.accProbA
  change (inner ℂ (hilbertTmul ψ ψ) (schrodingerQ m (hilbertTmul ψ ψ))).re = 1 ↔ _
  exact projection_expectation_one_iff (schrodingerQ m) (schrodingerQ_symmetric m)
    (schrodingerQ_idempotent m) (hilbertTmul ψ ψ) hn

/-- Unit acceptance supplies precisely the physical output factorization
used in the manuscript's coherent converse. -/
theorem coherent_factorization_of_acceptance_one {m : ℕ} (ψ : WaveSpace m)
    (hψ : ‖ψ‖ = 1) (hacc : schrodingerCoherentAcceptance ψ = 1) :
    ∃ φ : WaveSpace m,
      (schrodingerTensorRotation m (Real.pi/4)).symm (hilbertTmul ψ ψ) =
        hilbertTmul φ (waveVacuum m) := by
  have hfix := (schrodingerCoherentAcceptance_eq_one_iff_fixed ψ hψ).mp hacc
  apply exists_vacuum_factor_of_tensor_projection_fixed m
  have h := congrArg (schrodingerTensorRotation m (Real.pi/4)).symm hfix
  simpa only [schrodingerQ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] using h

/-- The physical coherent-test converse in Proposition 6.3, with equality
of pure-state density operators accounting for the irrelevant global phase. -/
theorem coherent_acceptance_one_eq_displaced_vacuum {m : ℕ} (ψ : WaveSpace m)
    (hψ : ‖ψ‖ = 1) (hacc : schrodingerCoherentAcceptance ψ = 1) :
    ∃ a : WavePhase m,
      InnerProductSpace.rankOne ℂ ψ ψ =
        InnerProductSpace.rankOne ℂ (weylOperator m a (waveVacuum m))
          (weylOperator m a (waveVacuum m)) := by
  obtain ⟨φ, hφ⟩ := coherent_factorization_of_acceptance_one ψ hψ hacc
  exact coherent_factorization_eq_displaced_vacuum m ψ φ hψ hφ

private theorem tensorRotation_inverse_vacuum (m : ℕ) (θ : ℝ) :
    (schrodingerTensorRotation m θ).symm (hilbertTmul (waveVacuum m) (waveVacuum m)) =
      hilbertTmul (waveVacuum m) (waveVacuum m) := by
  apply (schrodingerTensorRotation m θ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, schrodingerTensorRotation_vacuum]

/-- The inverse balanced splitter sends two identical displaced vacua to a
displaced vacuum in the first output and vacuum in the second. -/
theorem displaced_vacuum_factorization (m : ℕ) (a : WavePhase m) :
    (schrodingerTensorRotation m (Real.pi/4)).symm
        (hilbertTmul (weylOperator m a (waveVacuum m)) (weylOperator m a (waveVacuum m))) =
      hilbertTmul (weylOperator m (Real.sqrt 2 • a) (waveVacuum m)) (waveVacuum m) := by
  apply (schrodingerTensorRotation m (Real.pi/4)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have h := schrodingerTensorRotation_balanced_weyl m (Real.sqrt 2 • a) 0
    (hilbertTmul (waveVacuum m) (waveVacuum m))
  simpa only [tensorRotation_inverse_vacuum, tensorWeylOperator_tmul, weylOperator_zero,
    sub_zero, add_zero, smul_smul, inv_mul_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),
    one_smul] using h.symm

/-- Every physical coherent state is accepted with certainty. -/
theorem schrodingerCoherentAcceptance_displaced_vacuum (m : ℕ) (a : WavePhase m) :
    schrodingerCoherentAcceptance (weylOperator m a (waveVacuum m)) = 1 := by
  apply (schrodingerCoherentAcceptance_eq_one_iff_fixed _ (by
    rw [weylOperator_norm, waveVacuum_norm])).mpr
  simp only [schrodingerQ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, displaced_vacuum_factorization,
    hilbertTensorMap_tmul, ContinuousLinearMap.id_apply, waveVacuumProjection_apply,
    inner_self_eq_norm_sq_to_K, waveVacuum_norm, RCLike.ofReal_one, one_pow, one_smul]
  exact (congrArg (schrodingerTensorRotation m (Real.pi/4))
    (displaced_vacuum_factorization m a).symm).trans
      ((schrodingerTensorRotation m (Real.pi/4)).apply_symm_apply _)

/-- The coherent half of Proposition 6.3 on actual wavefunctions: unit
acceptance is equivalent to a displaced vacuum, up to global phase. -/
theorem schrodingerCoherentAcceptance_eq_one_iff {m : ℕ} (ψ : WaveSpace m)
    (hψ : ‖ψ‖ = 1) :
    schrodingerCoherentAcceptance ψ = 1 ↔
      ∃ (a : WavePhase m) (z : ℂ), ‖z‖ = 1 ∧ ψ = z • weylOperator m a (waveVacuum m) := by
  constructor
  · intro hacc
    obtain ⟨a, ha⟩ := coherent_acceptance_one_eq_displaced_vacuum ψ hψ hacc
    let v := weylOperator m a (waveVacuum m)
    let z := inner ℂ v ψ
    have hphase : ψ = z • v := by
      have h := congrArg (fun A : WaveSpace m →L[ℂ] WaveSpace m => A ψ) ha
      simpa only [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K,
        hψ, RCLike.ofReal_one, one_pow, one_smul] using h
    have hz : ‖z‖ = 1 := by
      have h := congrArg norm hphase
      simpa only [norm_smul, v, weylOperator_norm, waveVacuum_norm, mul_one, hψ] using h.symm
    exact ⟨a,z,hz,hphase⟩
  · rintro ⟨a,z,_,rfl⟩
    apply (schrodingerCoherentAcceptance_eq_one_iff_fixed _ hψ).mpr
    have hv : ‖weylOperator m a (waveVacuum m)‖ = 1 := by
      rw [weylOperator_norm, waveVacuum_norm]
    have hfix := (schrodingerCoherentAcceptance_eq_one_iff_fixed _ hv).mp
      (schrodingerCoherentAcceptance_displaced_vacuum m a)
    simp only [map_smul, _root_.smul_apply, hfix]

end
end GaussianTesting
