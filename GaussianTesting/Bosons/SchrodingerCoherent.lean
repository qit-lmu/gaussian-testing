module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerVacuum
public import GaussianTesting.Bosons.SchrodingerSwap

@[expose] public section

/-!
# The physical two-copy coherent-state test

The manuscript defines `Q = U_{π/4} (I ⊗ |0⟩⟨0|) U_{π/4}†` immediately
before Proposition 6.3. Here `Q` acts on the completed tensor square of actual
one-copy wavefunctions. Its range consists of symmetric two-copy vectors,
so it commutes with the swap as asserted in the manuscript. The acceptance
probability `q` is also the vacuum expectation of the reduced state after the
inverse rotation.

The characterization of certainty as coherence in Proposition 6.3 is a
separate result; this file constructs and verifies the measurement itself.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's physical coherent-state accepting projection `Q`. -/
def schrodingerQ (m : ℕ) :
    HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) :=
  (schrodingerTensorRotation m (Real.pi / 4)).conjStarAlgEquiv
    (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
      (waveVacuumProjection m))

theorem schrodingerQ_symmetric (m : ℕ) (x y : HilbertSquare (WaveSpace m)) :
    inner ℂ (schrodingerQ m x) y = inner ℂ x (schrodingerQ m y) := by
  let U := schrodingerTensorRotation m (Real.pi / 4)
  let P := hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
    (waveVacuumProjection m)
  have hQ (v : HilbertSquare (WaveSpace m)) : U.symm (schrodingerQ m v) = P (U.symm v) :=
    U.symm_apply_apply _
  calc
    _ = inner ℂ (U.symm (schrodingerQ m x)) (U.symm y) :=
      (U.symm.inner_map_map _ _).symm
    _ = inner ℂ (P (U.symm x)) (U.symm y) := congrArg (fun v => inner ℂ v (U.symm y)) (hQ x)
    _ = inner ℂ (U.symm x) (P (U.symm y)) :=
      hilbertTensorMap_symmetric _ _ (fun _ _ => rfl) (waveVacuumProjection_symmetric m) _ _
    _ = inner ℂ (U.symm x) (U.symm (schrodingerQ m y)) :=
      congrArg (inner ℂ (U.symm x)) (hQ y).symm
    _ = _ := U.symm.inner_map_map _ _

@[simp] theorem schrodingerQ_idempotent (m : ℕ) (x : HilbertSquare (WaveSpace m)) :
    schrodingerQ m (schrodingerQ m x) = schrodingerQ m x := by
  simp only [schrodingerQ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rw [hilbertTensorMap_idempotent _ _ (fun _ => rfl)
    (waveVacuumProjection_idempotent m)]

private theorem parity_vacuum_tensor (m : ℕ) (x : HilbertSquare (WaveSpace m)) :
    hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
        (waveParity m).toLinearIsometry.toContinuousLinearMap
        (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
          (waveVacuumProjection m) x) =
      hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
        (waveVacuumProjection m) x := by
  have h :
      (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
        (waveParity m).toLinearIsometry.toContinuousLinearMap).comp
        (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
          (waveVacuumProjection m)) =
        hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
          (waveVacuumProjection m) := by
    apply hilbertTensor_ext
    intro f g
    simp only [ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul,
      ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, waveParity_vacuumProjection]
  exact DFunLike.congr_fun h x

/-- Every vector in the range of the coherent-state projection is symmetric. -/
@[simp] theorem schrodingerQ_swap_left (m : ℕ) (x : HilbertSquare (WaveSpace m)) :
    hilbertSwap (schrodingerQ m x) = schrodingerQ m x := by
  simp only [schrodingerQ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    schrodingerTensorRotation_balanced_swap, parity_vacuum_tensor]

@[simp] theorem schrodingerQ_swap_right (m : ℕ) (x : HilbertSquare (WaveSpace m)) :
    schrodingerQ m (hilbertSwap x) = schrodingerQ m x := by
  apply ext_inner_left ℂ
  intro y
  calc
    inner ℂ y (schrodingerQ m (hilbertSwap x)) =
        inner ℂ (schrodingerQ m y) (hilbertSwap x) :=
      (schrodingerQ_symmetric m y (hilbertSwap x)).symm
    _ = inner ℂ (schrodingerQ m y) x := by
      simpa only [schrodingerQ_swap_left] using
        (hilbertSwap (E := WaveSpace m) (F := WaveSpace m)).inner_map_map
          (schrodingerQ m y) x
    _ = inner ℂ y (schrodingerQ m x) := schrodingerQ_symmetric m y x

/-- The physical `Q` is a symmetric idempotent commuting with copy swap. -/
theorem schrodingerQ_isAcceptance (m : ℕ) :
    (hilbertTensorSquare (WaveSpace m)).IsAcceptance (schrodingerQ m) := by
  refine ⟨schrodingerQ_symmetric m, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    exact schrodingerQ_idempotent m
  · intro x
    exact (schrodingerQ_swap_right m x).trans (schrodingerQ_swap_left m x).symm

/-- The manuscript's coherent-state test acceptance probability `q(ψ)`. -/
def schrodingerCoherentAcceptance {m : ℕ} (ψ : WaveSpace m) : ℝ :=
  (hilbertTensorSquare (WaveSpace m)).accProbA (schrodingerQ m) ψ

/-- The expectation defining `q` is real. -/
theorem schrodingerQ_expectation_real {m : ℕ} (ψ : WaveSpace m) :
    inner ℂ (hilbertTmul ψ ψ) (schrodingerQ m (hilbertTmul ψ ψ)) =
      (schrodingerCoherentAcceptance ψ : ℂ) :=
  (hilbertTensorSquare (WaveSpace m)).inner_tp_P_self (schrodingerQ_isAcceptance m) ψ

/-- A normalized wavefunction gives an acceptance probability between zero and one. -/
theorem schrodingerCoherentAcceptance_mem_Icc {m : ℕ} (ψ : WaveSpace m)
    (hψ : ‖ψ‖ = 1) : schrodingerCoherentAcceptance ψ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(hilbertTensorSquare (WaveSpace m)).accProbA_nonneg (schrodingerQ_isAcceptance m) ψ,
    (hilbertTensorSquare (WaveSpace m)).accProbA_le_one (schrodingerQ_isAcceptance m) hψ⟩

/-- The two-copy coherent-test expectation is the vacuum trace of the reduced
state after the inverse rotation, in any Hilbert basis. -/
theorem schrodingerQ_expectation_eq_reducedTrace {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) :
    inner ℂ (hilbertTmul ψ ψ) (schrodingerQ m (hilbertTmul ψ ψ)) =
      HilbertDensity.operatorTrace b (waveVacuumProjection m * schrodingerReducedState b ψ) := by
  let U := schrodingerTensorRotation m (Real.pi / 4)
  let v := hilbertTmul ψ ψ
  let P := hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
    (waveVacuumProjection m)
  have hQ : U.symm (schrodingerQ m v) = P (U.symm v) := U.symm_apply_apply _
  calc
    inner ℂ v (schrodingerQ m v) =
        inner ℂ (U.symm v) (U.symm (schrodingerQ m v)) :=
      (U.symm.inner_map_map _ _).symm
    _ = inner ℂ (U.symm v) (P (U.symm v)) := congrArg (inner ℂ (U.symm v)) hQ
    _ = _ := (HilbertDensity.operatorTrace_mul_reducedRight b b
      (U.symm v) (waveVacuumProjection m)).symm

theorem schrodingerCoherentAcceptance_eq_reducedTrace {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) :
    schrodingerCoherentAcceptance ψ =
      (HilbertDensity.operatorTrace b
        (waveVacuumProjection m * schrodingerReducedState b ψ)).re :=
  congrArg Complex.re (schrodingerQ_expectation_eq_reducedTrace b ψ)

/-- Equivalently, `q` is the vacuum matrix coefficient of the reduced state. -/
theorem schrodingerCoherentAcceptance_eq_vacuumExpectation {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) :
    schrodingerCoherentAcceptance ψ =
      (inner ℂ (waveVacuum m) (schrodingerReducedState b ψ (waveVacuum m))).re := by
  rw [schrodingerCoherentAcceptance_eq_reducedTrace b, waveVacuumProjection,
    HilbertDensity.operatorTrace_rankOne_mul]

end

end GaussianTesting
