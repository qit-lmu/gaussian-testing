module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.HilbertDensity
public import GaussianTesting.Bosons.WeylContinuity
public import Mathlib.Analysis.Normed.Group.FunctionSeries

@[expose] public section

/-!
# Characteristic functions on the Schrödinger space

The characteristic function is the complex trace `χρ(r) = Tr(ρ Dᵣ)`, in the
manuscript's product order. The basic trace properties follow from the
normalized summable Gram representation and the explicit unitary Weyl action.
Injectivity of the characteristic function is a separate result.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

section UnitaryTrace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {κ ι : Type*}

private theorem unitaryTrace_gramOp (b : HilbertBasis κ ℂ E)
    {g : ι → E} (hg : HilbertDensity.GramFam g) (U : E ≃ₗᵢ[ℂ] E) :
    HilbertDensity.operatorTrace b
        (HilbertDensity.gramOp b g hg * U.toLinearIsometry.toContinuousLinearMap) =
      ∑' i, inner ℂ (g i) (U (g i)) := by
  rw [← (HilbertDensity.isPositiveTraceClass_gramOp b hg).operatorTrace_mul_comm,
    HilbertDensity.operatorTrace_mul_gramOp]
  rfl

private theorem unitaryTrace_basis (b : HilbertBasis κ ℂ E)
    (c : HilbertBasis ι ℂ E) {ρ : E →L[ℂ] E}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) (U : E ≃ₗᵢ[ℂ] E) :
    HilbertDensity.operatorTrace c (ρ * U.toLinearIsometry.toContinuousLinearMap) =
      HilbertDensity.operatorTrace b (ρ * U.toLinearIsometry.toContinuousLinearMap) := by
  have hc := (HilbertDensity.isPositiveTraceClass_basis_iff b c ρ).mp hρ
  rw [← hc.operatorTrace_mul_comm, hρ.operatorTrace_basis,
    hρ.operatorTrace_mul_comm]

private theorem norm_unitaryTrace_le_one (b : HilbertBasis κ ℂ E)
    {ρ : E →L[ℂ] E} (hρ : HilbertDensity.IsDensityOperator b ρ)
    (U : E ≃ₗᵢ[ℂ] E) :
    ‖HilbertDensity.operatorTrace b (ρ * U.toLinearIsometry.toContinuousLinearMap)‖ ≤ 1 := by
  rw [← hρ.toIsPositiveTraceClass.operatorTrace_mul_comm]
  exact (hρ.toIsPositiveTraceClass.norm_operatorTrace_mul_le _).trans
    (by simpa only [hρ.trace_eq_one, mul_one] using
      U.toLinearIsometry.norm_toContinuousLinearMap_le)

private theorem unitaryTrace_symm (b : HilbertBasis κ ℂ E)
    {ρ : E →L[ℂ] E} (hρ : HilbertDensity.IsPositiveTraceClass b ρ)
    (U : E ≃ₗᵢ[ℂ] E) :
    HilbertDensity.operatorTrace b (ρ * U.symm.toLinearIsometry.toContinuousLinearMap) =
      star (HilbertDensity.operatorTrace b (ρ * U.toLinearIsometry.toContinuousLinearMap)) := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  rw [unitaryTrace_gramOp b hg, unitaryTrace_gramOp b hg]
  change _ = (starRingEnd ℂ) (∑' i, inner ℂ (g i) (U (g i)))
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro i
  rw [← U.inner_map_map (g i) (U.symm (g i)), U.apply_symm_apply]
  exact (inner_conj_symm (𝕜 := ℂ) (U (g i)) (g i)).symm

private theorem continuous_unitaryTrace {X : Type*} [TopologicalSpace X]
    (b : HilbertBasis κ ℂ E) {ρ : E →L[ℂ] E}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) (U : X → E ≃ₗᵢ[ℂ] E)
    (hU : ∀ x, Continuous (fun r => U r x)) :
    Continuous (fun r => HilbertDensity.operatorTrace b
      (ρ * (U r).toLinearIsometry.toContinuousLinearMap)) := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  simp_rw [unitaryTrace_gramOp b hg]
  apply continuous_tsum (fun i => continuous_const.inner (𝕜 := ℂ) (hU (g i))) hg
  intro i r
  calc
    ‖inner ℂ (g i) (U r (g i))‖ ≤ ‖g i‖ * ‖U r (g i)‖ := norm_inner_le_norm _ _
    _ = ‖g i‖ ^ 2 := by rw [(U r).norm_map]; ring

end UnitaryTrace

variable {m : ℕ} {κ ι : Type*}

/-- The manuscript's characteristic function `χρ(r) = Tr(ρ Dᵣ)` on the actual
Schrödinger Hilbert space. A basis is supplied only to define the trace;
`waveCharacteristic_basis` proves independence for positive trace-class states. -/
def waveCharacteristic (b : HilbertBasis κ ℂ (WaveSpace m))
    (ρ : WaveSpace m →L[ℂ] WaveSpace m) (r : WavePhase m) : ℂ :=
  HilbertDensity.operatorTrace b
    (ρ * (weylOperator m r).toLinearIsometry.toContinuousLinearMap)

/-- The characteristic function is the convergent Gram expectation of the
explicit Weyl action. -/
theorem waveCharacteristic_gramOp (b : HilbertBasis κ ℂ (WaveSpace m))
    {g : ι → WaveSpace m} (hg : HilbertDensity.GramFam g) (r : WavePhase m) :
    waveCharacteristic b (HilbertDensity.gramOp b g hg) r =
      ∑' i, inner ℂ (g i) (weylOperator m r (g i)) :=
  unitaryTrace_gramOp b hg (weylOperator m r)

/-- Positive trace-class states have a basis-independent characteristic function. -/
theorem waveCharacteristic_basis (b : HilbertBasis κ ℂ (WaveSpace m))
    (c : HilbertBasis ι ℂ (WaveSpace m)) {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) (r : WavePhase m) :
    waveCharacteristic c ρ r = waveCharacteristic b ρ r :=
  unitaryTrace_basis b c hρ (weylOperator m r)

/-- A density operator has characteristic function one at zero displacement. -/
@[simp] theorem waveCharacteristic_zero (b : HilbertBasis κ ℂ (WaveSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsDensityOperator b ρ) : waveCharacteristic b ρ 0 = 1 := by
  have hD : (weylOperator m 0).toLinearIsometry.toContinuousLinearMap =
      (1 : WaveSpace m →L[ℂ] WaveSpace m) := by
    apply ContinuousLinearMap.ext
    intro f
    exact weylOperator_zero m f
  rw [waveCharacteristic, hD, mul_one,
    hρ.toIsPositiveTraceClass.operatorTrace_eq_positiveTrace, hρ.trace_eq_one]
  rfl

/-- The modulus of a density operator's characteristic function is at most one. -/
theorem norm_waveCharacteristic_le_one (b : HilbertBasis κ ℂ (WaveSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsDensityOperator b ρ) (r : WavePhase m) :
    ‖waveCharacteristic b ρ r‖ ≤ 1 :=
  norm_unitaryTrace_le_one b hρ (weylOperator m r)

/-- Reversing a displacement conjugates the characteristic function. -/
theorem waveCharacteristic_neg (b : HilbertBasis κ ℂ (WaveSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) (r : WavePhase m) :
    waveCharacteristic b ρ (-r) = star (waveCharacteristic b ρ r) := by
  unfold waveCharacteristic
  rw [← weylOperator_symm_neg]
  exact unitaryTrace_symm b hρ (weylOperator m r)

/-- A positive trace-class state's characteristic function is continuous on
the full phase space. The uniformly summable Gram bound uses strong continuity
of the Weyl family, and does not assume operator-norm continuity. -/
theorem continuous_waveCharacteristic (b : HilbertBasis κ ℂ (WaveSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) :
    Continuous (waveCharacteristic b ρ) :=
  continuous_unitaryTrace b hρ (weylOperator m) (continuous_weylOperator m)

end
end GaussianTesting
