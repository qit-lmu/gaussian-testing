module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PhysicalMeanZero
public import GaussianTesting.Bosons.NumberProjection

@[expose] public section

/-! # Acceptance conditions for the physical mean-zero test -/

namespace GaussianTesting

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

/-- The physical closed-kernel projection satisfies the two-copy acceptance
conditions, including invariance under swapping the copies. -/
theorem schrodingerTensorP0_isAcceptance (m : ℕ) :
    (hilbertTensorSquare (WaveSpace m)).IsAcceptance (schrodingerTensorP0 m) := by
  constructor
  · exact schrodingerTensorP0_symmetric m
  · ext v : 1
    exact schrodingerTensorP0_idempotent m v
  · intro v
    apply (waveNumberCoordinates m).injective
    change waveNumberCoordinates m (schrodingerTensorP0 m
      ((hilbertTensorSquare (WaveSpace m)).swap v)) =
      waveNumberCoordinates m ((hilbertTensorSquare (WaveSpace m)).swap
        (schrodingerTensorP0 m v))
    rw [waveNumberCoordinates_P0]
    simp only [waveNumberCoordinates, hilbertCoords_swap]
    rw [(P0B_isAcceptance m).swap_comm]
    exact congrArg (lpTensorSquare (Fin m → ℕ)).swap (waveNumberCoordinates_P0 m v).symm

/-- The mean-zero physical test defines a probability on unit vectors. -/
theorem schrodingerMeanZeroAcceptance_mem_Icc {m : ℕ} (ψ : WaveSpace m)
    (hψ : ‖ψ‖ = 1) : schrodingerMeanZeroAcceptance ψ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(hilbertTensorSquare (WaveSpace m)).accProbA_nonneg (schrodingerTensorP0_isAcceptance m) ψ,
    (hilbertTensorSquare (WaveSpace m)).accProbA_le_one (schrodingerTensorP0_isAcceptance m) hψ⟩

end
end GaussianTesting
