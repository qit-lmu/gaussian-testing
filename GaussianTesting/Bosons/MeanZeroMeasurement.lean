module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.EqualNumberProjection
public import GaussianTesting.Bosons.NumberCoherent
public import GaussianTesting.Bosons.PhysicalMeanZero

@[expose] public section

/-!
# The physical equal-number circuit of Figure 1(b)

The phase shift on every mode of register two is defined by its diagonal
action in the proved complete oscillator number basis: occupation `q`
is multiplied by `(-i)^|q|`. It is followed by the manuscript's actual
positive-angle balanced splitter. Accepting equal total counts gives
exactly the physical closed-kernel projection `P₀`.
-/

namespace GaussianTesting

open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

/-- Shift every second-register mode by π/2, with phase `exp(-iπN₂/2)`
specified directly in the physical oscillator number basis. -/
def waveSecondRegisterPhase (m : ℕ) :
    HilbertSquare (WaveSpace m) ≃ₗᵢ[ℂ] HilbertSquare (WaveSpace m) :=
  (waveNumberCoordinates m).trans
    ((numberPhase m (-Complex.I) (by simp)).trans (waveNumberCoordinates m).symm)

/-- The phase leaves all first-register occupations unchanged and gives
exactly the prescribed phase to the total count of register two. -/
theorem waveSecondRegisterPhase_numberCoordinates (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    waveNumberCoordinates m (waveSecondRegisterPhase m v) p =
      (-Complex.I) ^ degB p.2 * waveNumberCoordinates m v p := by
  simp only [waveSecondRegisterPhase, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, numberPhase_apply]

/-- The exact gate order in Figure 1(b): phase register two, then apply
`U_{π/4}` to the two registers. -/
def meanZeroNumberCircuit (m : ℕ) :
    HilbertSquare (WaveSpace m) ≃ₗᵢ[ℂ] HilbertSquare (WaveSpace m) :=
  (waveSecondRegisterPhase m).trans (schrodingerTensorRotation m (Real.pi / 4))

/-- The event that the two measured total counts agree, in the physical
number basis of the two-copy Hilbert space. -/
def waveEqualTotalNumberProjection (m : ℕ) :
    HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) :=
  (waveNumberCoordinates m).symm.conjStarAlgEquiv (equalTotalNumberProjection m)

private theorem numberCoordinates_meanZeroCircuit (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m (meanZeroNumberCircuit m v) =
      (equalNumberCircuitInverse m).symm (waveNumberCoordinates m v) := by
  simp only [meanZeroNumberCircuit, LinearIsometryEquiv.trans_apply,
    waveNumberCoordinates_rotation, waveSecondRegisterPhase,
    LinearIsometryEquiv.apply_symm_apply, equalNumberCircuitInverse,
    LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_symm, numberPhase_I_symm]
  rfl

private theorem numberCoordinates_meanZeroCircuit_symm (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m ((meanZeroNumberCircuit m).symm v) =
      equalNumberCircuitInverse m (waveNumberCoordinates m v) := by
  simp only [meanZeroNumberCircuit, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, waveSecondRegisterPhase,
    LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    numberPhase_negI_symm, waveNumberCoordinates_rotation_symm,
    equalNumberCircuitInverse, LinearIsometryEquiv.trans_apply]
  rfl

private theorem numberCoordinates_equalTotalNumberProjection (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m (waveEqualTotalNumberProjection m v) =
      equalTotalNumberProjection m (waveNumberCoordinates m v) := by
  simp only [waveEqualTotalNumberProjection, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]

/-- Figure 1(b)'s accepting projection: run the physical phase/splitter
circuit and retain exactly outcomes with equal total particle counts. -/
def meanZeroNumberMeasurement (m : ℕ) :
    HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) :=
  (meanZeroNumberCircuit m).symm.conjStarAlgEquiv (waveEqualTotalNumberProjection m)

/-- **Figure 1(b).** The count-readout circuit has precisely the physical
closed-kernel accepting observable used throughout Section 6. -/
theorem meanZeroNumberMeasurement_eq_P0 (m : ℕ) :
    meanZeroNumberMeasurement m = schrodingerTensorP0 m := by
  ext v : 1
  apply (waveNumberCoordinates m).injective
  change waveNumberCoordinates m ((meanZeroNumberCircuit m).symm
    (waveEqualTotalNumberProjection m (meanZeroNumberCircuit m v))) = _
  rw [numberCoordinates_meanZeroCircuit_symm, numberCoordinates_equalTotalNumberProjection,
    numberCoordinates_meanZeroCircuit, waveNumberCoordinates_P0]
  exact DFunLike.congr_fun (equalNumberCircuit_conj_projection m) (waveNumberCoordinates m v)

/-- The explicit physical readout accepts with the manuscript's `p₀(ψ)`. -/
theorem meanZeroNumberMeasurement_acceptance {m : ℕ} (ψ : WaveSpace m) :
    (inner ℂ (hilbertTmul ψ ψ)
      (meanZeroNumberMeasurement m (hilbertTmul ψ ψ))).re =
        schrodingerMeanZeroAcceptance ψ := by
  rw [meanZeroNumberMeasurement_eq_P0 m]
  rfl

end
end GaussianTesting
