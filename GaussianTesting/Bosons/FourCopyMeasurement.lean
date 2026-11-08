module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerCircuitSwap
public import GaussianTesting.Bosons.MeanZeroMeasurement

@[expose] public section

/-!
# The wiring of Figure 1(d)

The figure applies a negative-angle balanced splitter to each pair of inputs
and tests the retained registers (2,4). Regrouping the outputs as discarded
registers (1,3) and retained registers (2,4) gives exactly the Section 6
four-copy projection, on the full input Hilbert space. The physical readout
from Figure 1(b) realizes the same accepting operator.
-/

namespace GaussianTesting

open scoped InnerProductSpace
noncomputable section
set_option maxRecDepth 2048

/-- Figure 1(d) applies `U_{-π/4}` to each pair and groups the discarded
registers (1,3) and retained difference outputs (2,4). -/
def fourCopyFigurePreparation (m : ℕ) : HilbertFourth (WaveSpace m) ≃ₗᵢ[ℂ]
    HilbertFourth (WaveSpace m) :=
  (hilbertTensorEquiv (schrodingerTensorRotation m (-(Real.pi / 4)))
    (schrodingerTensorRotation m (-(Real.pi / 4)))).trans hilbertReshuffle

/-- The physical splitter angles and retained-wire ordering are exactly
those drawn in Figure 1(d). -/
theorem fourCopyFigurePreparation_explicit (m : ℕ) :
    fourCopyFigurePreparation m =
      (hilbertTensorEquiv (schrodingerTensorRotation m (-(Real.pi / 4)))
        (schrodingerTensorRotation m (-(Real.pi / 4)))).trans hilbertReshuffle := rfl

/-- Figure 1(d)'s preparation is the Section 6 inverse-splitter preparation
on the full four-copy Hilbert space. -/
theorem fourCopyFigurePreparation_eq (m : ℕ) :
    fourCopyFigurePreparation m =
      fourCopyPreparation (schrodingerTensorRotation m (Real.pi / 4)) := by
  simp only [fourCopyFigurePreparation, fourCopyPreparation, schrodingerTensorRotation_symm]

/-- In particular, the preparations agree on four identical wavefunctions. -/
theorem fourCopyFigurePreparation_input (m : ℕ) (ψ : WaveSpace m) :
    fourCopyFigurePreparation m (fourCopyInput ψ) =
      fourCopyPreparation (schrodingerTensorRotation m (Real.pi / 4)) (fourCopyInput ψ) :=
  DFunLike.congr_fun (fourCopyFigurePreparation_eq m) (fourCopyInput ψ)

/-- Figure 1(d)'s accepting event, with the physical mean-zero projection
on the retained registers (2,4). -/
def fourCopyFigureProjection (m : ℕ) :
    HilbertFourth (WaveSpace m) →L[ℂ] HilbertFourth (WaveSpace m) :=
  (fourCopyFigurePreparation m).symm.conjStarAlgEquiv
    (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare (WaveSpace m)))
      (schrodingerTensorP0 m))

/-- **Figure 1(d).** Its accepting projection equals the Section 6 operator
on arbitrary four-copy inputs. -/
theorem fourCopyFigureProjection_eq (m : ℕ) :
    fourCopyFigureProjection m = schrodingerFourCopyProjection m :=
  congrArg (fun V : HilbertFourth (WaveSpace m) ≃ₗᵢ[ℂ] HilbertFourth (WaveSpace m) =>
    V.symm.conjStarAlgEquiv
      (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare (WaveSpace m)))
        (schrodingerTensorP0 m))) (fourCopyFigurePreparation_eq m)

/-- **Figure 1(d).** The circuit has the manuscript's acceptance probability
on four identical inputs. -/
theorem fourCopyFigureProjection_acceptance {m : ℕ} (ψ : WaveSpace m) :
    (inner ℂ (fourCopyInput ψ) (fourCopyFigureProjection m (fourCopyInput ψ))).re =
      schrodingerFourCopyAcceptance ψ :=
  congrArg (fun A : HilbertFourth (WaveSpace m) →L[ℂ] HilbertFourth (WaveSpace m) =>
    (inner ℂ (fourCopyInput ψ) (A (fourCopyInput ψ))).re)
    (fourCopyFigureProjection_eq m)

/-- The complete Figure 1(d) accepting event, using the phase/splitter and
equal-count readout of Figure 1(b) on the retained registers (2,4). -/
def fourCopyNumberMeasurement (m : ℕ) :
    HilbertFourth (WaveSpace m) →L[ℂ] HilbertFourth (WaveSpace m) :=
  (fourCopyFigurePreparation m).symm.conjStarAlgEquiv
    (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare (WaveSpace m)))
      (meanZeroNumberMeasurement m))

/-- The explicit count-readout circuit is exactly the Figure 1(d) projection. -/
theorem fourCopyNumberMeasurement_eq_figureProjection (m : ℕ) :
    fourCopyNumberMeasurement m = fourCopyFigureProjection m :=
  congrArg (fun P : HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) =>
    (fourCopyFigurePreparation m).symm.conjStarAlgEquiv
      (hilbertTensorMap (ContinuousLinearMap.id ℂ (HilbertSquare (WaveSpace m))) P))
    (meanZeroNumberMeasurement_eq_P0 m)

/-- **Figure 1(d).** The full readout circuit realizes exactly the Section 6
four-copy accepting operator, without a restriction to identical inputs. -/
theorem fourCopyNumberMeasurement_eq_projection (m : ℕ) :
    fourCopyNumberMeasurement m = schrodingerFourCopyProjection m :=
  (fourCopyNumberMeasurement_eq_figureProjection m).trans (fourCopyFigureProjection_eq m)

/-- **Figure 1(d).** All gates, the retained-wire choice, and the equal-number
readout give precisely the manuscript's four-copy acceptance probability. -/
theorem fourCopyNumberMeasurement_acceptance {m : ℕ} (ψ : WaveSpace m) :
    (inner ℂ (fourCopyInput ψ) (fourCopyNumberMeasurement m (fourCopyInput ψ))).re =
      schrodingerFourCopyAcceptance ψ :=
  congrArg (fun A : HilbertFourth (WaveSpace m) →L[ℂ] HilbertFourth (WaveSpace m) =>
    (inner ℂ (fourCopyInput ψ) (A (fourCopyInput ψ))).re)
    (fourCopyNumberMeasurement_eq_projection m)

end
end GaussianTesting
