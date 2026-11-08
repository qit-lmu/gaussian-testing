module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerTensorUnitary
public import GaussianTesting.Bosons.SchrodingerPurity
public import GaussianTesting.Bosons.FourCopyProjection
public import GaussianTesting.Bosons.PartialTrace

@[expose] public section

/-!
# The physical four-copy bosonic measurement

This file constructs the accepting projection preceding Proposition 6.3 on
four copies of the actual Schrödinger space. The unitary `waveTensorEquiv`
identifies two-copy wavefunctions with their completed Hilbert tensor product;
the rotation and the kernel projection are the manuscript's actual `U_θ`
and `P₀` under that identification.

The acceptance identity uses the reduced state on register two after applying
`U_{π/4}†`, exactly as in the converse direction of Proposition 6.3.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's `U_θ` on the completed tensor square of one-copy
wavefunctions, transported through the canonical wavefunction equivalence. -/
def schrodingerTensorRotation (m : ℕ) (θ : ℝ) :
    HilbertSquare (WaveSpace m) ≃ₗᵢ[ℂ] HilbertSquare (WaveSpace m) :=
  (waveTensorEquiv m).trans ((schrodingerRotation m θ).trans (waveTensorEquiv m).symm)

/-- The physical closed-kernel projection `P₀` in tensor-product coordinates. -/
def schrodingerTensorP0 (m : ℕ) :
    HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) :=
  (waveTensorEquiv m).symm.conjStarAlgEquiv (schrodingerP0 m)

theorem schrodingerTensorP0_symmetric (m : ℕ)
    (x y : HilbertSquare (WaveSpace m)) :
    inner ℂ (schrodingerTensorP0 m x) y = inner ℂ x (schrodingerTensorP0 m y) := by
  calc
    _ = inner ℂ (waveTensorEquiv m (schrodingerTensorP0 m x)) (waveTensorEquiv m y) :=
      ((waveTensorEquiv m).inner_map_map _ _).symm
    _ = inner ℂ (waveTensorEquiv m x) (waveTensorEquiv m (schrodingerTensorP0 m y)) := by
      simpa only [schrodingerTensorP0, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply] using
        schrodingerP0_symmetric m (waveTensorEquiv m x) (waveTensorEquiv m y)
    _ = _ := (waveTensorEquiv m).inner_map_map _ _

theorem schrodingerTensorP0_idempotent (m : ℕ)
    (x : HilbertSquare (WaveSpace m)) :
    schrodingerTensorP0 m (schrodingerTensorP0 m x) = schrodingerTensorP0 m x := by
  simp only [schrodingerTensorP0, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    schrodingerP0_idempotent]

/-- The manuscript's four-copy accepting projection
`U_{π/4}⊗² P₀,₂₄ (U_{π/4}†)⊗²` on actual one-copy wavefunctions. -/
def schrodingerFourCopyProjection (m : ℕ) :
    HilbertFourth (WaveSpace m) →L[ℂ] HilbertFourth (WaveSpace m) :=
  fourCopyProjection (schrodingerTensorRotation m (Real.pi / 4)) (schrodingerTensorP0 m)

theorem schrodingerFourCopyProjection_symmetric (m : ℕ)
    (x y : HilbertFourth (WaveSpace m)) :
    inner ℂ (schrodingerFourCopyProjection m x) y =
      inner ℂ x (schrodingerFourCopyProjection m y) :=
  fourCopyProjection_symmetric (schrodingerTensorRotation m (Real.pi / 4))
    (schrodingerTensorP0 m) (schrodingerTensorP0_symmetric m) x y

theorem schrodingerFourCopyProjection_idempotent (m : ℕ)
    (x : HilbertFourth (WaveSpace m)) :
    schrodingerFourCopyProjection m (schrodingerFourCopyProjection m x) =
      schrodingerFourCopyProjection m x :=
  fourCopyProjection_idempotent (schrodingerTensorRotation m (Real.pi / 4))
    (schrodingerTensorP0 m) (schrodingerTensorP0_idempotent m) x

/-- The manuscript's `p(ψ)`, defined by the expectation of the four-copy
accepting projection on four identical copies of the input wavefunction. -/
def schrodingerFourCopyAcceptance {m : ℕ} (ψ : WaveSpace m) : ℝ :=
  fourCopyAcceptance (schrodingerTensorRotation m (Real.pi / 4)) (schrodingerTensorP0 m) ψ

/-- The reduced state on register two after the inverse `π/4` rotation. -/
def schrodingerReducedState {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) :
    WaveSpace m →L[ℂ] WaveSpace m :=
  HilbertDensity.reducedRight b b
    ((schrodingerTensorRotation m (Real.pi / 4)).symm (hilbertTmul ψ ψ))

theorem schrodingerReducedState_positiveTraceClass {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) :
    HilbertDensity.IsPositiveTraceClass b (schrodingerReducedState b ψ) :=
  HilbertDensity.isPositiveTraceClass_reducedRight b b _

/-- A unit input gives a positive trace-class reduced operator of trace one. -/
theorem schrodingerReducedState_isDensityOperator {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    HilbertDensity.IsDensityOperator b (schrodingerReducedState b ψ) := by
  apply HilbertDensity.isDensityOperator_reducedRight
  simp only [LinearIsometryEquiv.norm_map, HilbertDensity.norm_hilbertTmul, hψ, one_mul]

/-- The reduced physical operator does not depend on the coordinate basis. -/
theorem schrodingerReducedState_basis {m : ℕ} {κ κ' : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (b' : HilbertBasis κ' ℂ (WaveSpace m))
    (ψ : WaveSpace m) :
    schrodingerReducedState b ψ = schrodingerReducedState b' ψ :=
  HilbertDensity.reducedRight_basis b b b' b' _

private theorem tensor_trace_transport {E H κ ν : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {b : HilbertBasis κ ℂ E} (c : HilbertBasis ν ℂ H)
    {ρ : E →L[ℂ] E} (hρ : HilbertDensity.IsPositiveTraceClass b ρ)
    (T : HilbertSquare E ≃ₗᵢ[ℂ] H) (P : H →L[ℂ] H) :
    HilbertDensity.operatorTrace (HilbertDensity.tensorBasis b)
        (T.symm.conjStarAlgEquiv P * hilbertTensorMap ρ ρ) =
      HilbertDensity.operatorTrace c (P * HilbertDensity.embeddedTensor T.toLinearIsometry ρ) := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  rw [HilbertDensity.embeddedTensor_eq_gramOp b c hg,
    ← HilbertDensity.gramOp_tensor b hg,
    HilbertDensity.operatorTrace_mul_gramOp, HilbertDensity.operatorTrace_mul_gramOp]
  apply tsum_congr
  intro p
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.coe_toLinearIsometry] using
    (T.inner_map_map (hilbertTmul (g p.1) (g p.2))
      (T.symm.conjStarAlgEquiv P (hilbertTmul (g p.1) (g p.2)))).symm

/-- The tensor-coordinate trace is the trace against the actual physical
kernel projection, in any Hilbert basis of two-copy wavefunctions. -/
theorem schrodingerTensorP0_trace {m : ℕ} {κ ν : Type*}
    {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) :
    HilbertDensity.operatorTrace (HilbertDensity.tensorBasis b)
        (schrodingerTensorP0 m * hilbertTensorMap ρ ρ) =
      HilbertDensity.operatorTrace c (schrodingerP0 m * schrodingerDensityTensor m ρ) :=
  tensor_trace_transport c hρ (waveTensorEquiv m) (schrodingerP0 m)

/-- The four-copy Born expectation equals `Tr[P₀ ρ⊗²]`, as used in
Proposition 6.3, with `ρ` obtained from the actual inverse rotation.
This is an equality of complex numbers, in arbitrary coordinate bases. -/
theorem schrodingerFourCopyProjection_expectation_eq_reducedTrace {m : ℕ} {κ ν : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (c : HilbertBasis ν ℂ (SchrodingerSpace m)) (ψ : WaveSpace m) :
    inner ℂ (fourCopyInput ψ) (schrodingerFourCopyProjection m (fourCopyInput ψ)) =
      HilbertDensity.operatorTrace c
        (schrodingerP0 m * schrodingerDensityTensor m (schrodingerReducedState b ψ)) :=
  (fourCopyProjection_expectation_eq_reducedTrace b
    (schrodingerTensorRotation m (Real.pi / 4)) (schrodingerTensorP0 m) ψ).trans
      (schrodingerTensorP0_trace c (schrodingerReducedState_positiveTraceClass b ψ))

/-- The reduced-state identity for the manuscript's acceptance probability. -/
theorem schrodingerFourCopyAcceptance_eq_reducedTrace {m : ℕ} {κ ν : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (c : HilbertBasis ν ℂ (SchrodingerSpace m)) (ψ : WaveSpace m) :
    schrodingerFourCopyAcceptance ψ =
      (HilbertDensity.operatorTrace c
        (schrodingerP0 m * schrodingerDensityTensor m (schrodingerReducedState b ψ))).re :=
  congrArg Complex.re (schrodingerFourCopyProjection_expectation_eq_reducedTrace b c ψ)

/-- For a unit input, the four-copy test acceptance is a probability. -/
theorem schrodingerFourCopyAcceptance_mem_Icc {m : ℕ} {κ ν : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (c : HilbertBasis ν ℂ (SchrodingerSpace m)) (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerFourCopyAcceptance ψ ∈ Set.Icc (0 : ℝ) 1 := by
  have hρ := schrodingerReducedState_isDensityOperator b ψ hψ
  rw [schrodingerFourCopyAcceptance_eq_reducedTrace b c, schrodingerDensityTensor,
    (hρ.embeddedTensor c (waveTensor m)).toIsPositiveTraceClass.operatorTrace_mul_comm]
  exact schrodinger_acceptance_mem_Icc c hρ

end
end GaussianTesting
