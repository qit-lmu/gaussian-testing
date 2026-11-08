module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.HilbertDensity
public import GaussianTesting.PureStateDifference
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

@[expose] public section

/-!
# Pure-state trace distance

The trace norm is the trace of the positive operator `|A| = sqrt(A†A)`.
For differences of unit rank-one projections, its trace is finite and equals
twice the square root of the overlap deficit, on any complex Hilbert space.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

local instance : NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

/-- The standard trace norm, evaluated as `Tr sqrt(A†A)` in a Hilbert basis.
It is used below only after proving the positive modulus is trace class. -/
def traceNorm (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E) : ℝ :=
  HilbertDensity.positiveTrace b (CFC.abs A)

omit [CompleteSpace E] in
private theorem rankOne_diagonal_hasSum (b : HilbertBasis ι ℂ E) (x y : E) :
    HasSum (fun i => inner ℂ (b i) (InnerProductSpace.rankOne ℂ x y (b i)))
      (inner ℂ y x) := by
  simpa only [InnerProductSpace.rankOne_apply, inner_smul_right, mul_comm] using
    b.hasSum_inner_mul_inner y x

omit [CompleteSpace E] in
private theorem overlap_deficit_nonneg (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    0 ≤ 1 - ‖inner ℂ ψ φ‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) ψ φ
  rw [hψ, hφ, one_mul] at h
  nlinarith [norm_nonneg (inner ℂ ψ φ)]

omit [CompleteSpace E] in
private theorem pureStateDifference_sq_hasSum (b : HilbertBasis ι ℂ E)
    (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    HasSum (fun i => (inner ℂ (b i) ((pureStateDifference ψ φ ^ 2) (b i))).re)
      (2 * (1 - ‖inner ℂ ψ φ‖ ^ 2)) := by
  have h := ((rankOne_diagonal_hasSum b ψ ψ).add (rankOne_diagonal_hasSum b φ φ)).sub
    ((rankOne_diagonal_hasSum b ψ φ).mul_left (inner ℂ ψ φ))
  have h' := h.sub ((rankOne_diagonal_hasSum b φ ψ).mul_left (inner ℂ φ ψ))
  have hq : inner ℂ ψ φ * inner ℂ φ ψ = (‖inner ℂ ψ φ‖ ^ 2 : ℂ) := by
    rw [← inner_conj_symm φ ψ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hc : inner ℂ ψ ψ + inner ℂ φ φ - inner ℂ ψ φ * inner ℂ φ ψ -
      inner ℂ φ ψ * inner ℂ ψ φ = (2 * (1 - ‖inner ℂ ψ φ‖ ^ 2) : ℝ) := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hψ, hφ]
    rw [mul_comm (inner ℂ φ ψ), hq]
    push_cast
    ring
  rw [hc] at h'
  simpa only [pureStateDifference_sq ψ φ hψ hφ, add_apply,
    sub_apply, smul_apply, inner_add_right,
    inner_sub_right, inner_smul_right, Complex.ofReal_re] using Complex.hasSum_re h'

/-- The absolute value of the rank-one difference is a nonnegative multiple
of its square. The zero-overlap-deficit case is included. -/
theorem abs_pureStateDifference (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    CFC.abs (pureStateDifference ψ φ) =
      (Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2))⁻¹ • pureStateDifference ψ φ ^ 2 := by
  let s := Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - ‖inner ℂ ψ φ‖ ^ 2 :=
    Real.sq_sqrt (overlap_deficit_nonneg ψ φ hψ hφ)
  by_cases hs : s = 0
  · have hq : ‖inner ℂ ψ φ‖ ^ 2 = 1 := by rw [hs] at hs2; nlinarith
    rw [pureStateDifference_eq_zero_of_overlap_sq_eq_one ψ φ hψ hφ hq]
    simp
  · change CFC.sqrt (star (pureStateDifference ψ φ) * pureStateDifference ψ φ) =
      s⁻¹ • pureStateDifference ψ φ ^ 2
    rw [(pureStateDifference_isSelfAdjoint ψ φ).star_eq, ← pow_two]
    apply CFC.sqrt_unique
    · rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add,
        show (2 : ℕ) + 2 = 4 by rfl, pureStateDifference_fourth ψ φ hψ hφ,
        smul_smul]
      have he : s⁻¹ * s⁻¹ * (1 - ‖inner ℂ ψ φ‖ ^ 2) = 1 := by
        rw [← hs2]
        field_simp
      rw [he, one_smul]
    · exact smul_nonneg (inv_nonneg.mpr hs0) (pureStateDifference_sq_nonneg ψ φ)

private theorem abs_pureStateDifference_hasSum (b : HilbertBasis ι ℂ E)
    (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    HasSum (fun i => (inner ℂ (b i) (CFC.abs (pureStateDifference ψ φ) (b i))).re)
      (2 * Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2)) := by
  let s := Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2)
  have hs2 : s ^ 2 = 1 - ‖inner ℂ ψ φ‖ ^ 2 :=
    Real.sq_sqrt (overlap_deficit_nonneg ψ φ hψ hφ)
  have h := (pureStateDifference_sq_hasSum b ψ φ hψ hφ).mul_left s⁻¹
  have he : s⁻¹ * (2 * (1 - ‖inner ℂ ψ φ‖ ^ 2)) = 2 * s := by
    rw [← hs2]
    by_cases hs : s = 0
    · simp [hs]
    · field_simp
  rw [he] at h
  simpa only [abs_pureStateDifference ψ φ hψ hφ, smul_apply,
    inner_smul_right_eq_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, s] using h

/-- The modulus of a difference of pure-state density operators is positive
trace class. Thus the trace norm below is an actual finite operator trace. -/
theorem isPositiveTraceClass_abs_pureStateDifference (b : HilbertBasis ι ℂ E)
    (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    HilbertDensity.IsPositiveTraceClass b (CFC.abs (pureStateDifference ψ φ)) :=
  ⟨CFC.abs_nonneg _, (abs_pureStateDifference_hasSum b ψ φ hψ hφ).summable⟩

/-- The trace norm of the difference of unit rank-one projections, in every
Hilbert basis. This is valid in infinite as well as finite dimension. -/
theorem traceNorm_pureStateDifference (b : HilbertBasis ι ℂ E)
    (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm b (pureStateDifference ψ φ) =
      2 * Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2) :=
  (abs_pureStateDifference_hasSum b ψ φ hψ hφ).tsum_eq

def traceBasisCarrier (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : Set E :=
  (exists_hilbertBasis ℂ E).choose

def traceBasis (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :
    HilbertBasis (traceBasisCarrier E) ℂ E :=
  (exists_hilbertBasis ℂ E).choose_spec.choose

/-- Pure-state trace distance is half the trace norm of the difference of the
rank-one density operators. The chosen Hilbert basis is immaterial for unit
inputs, as proved below; this is not a definition in terms of overlap. -/
def pureStateTraceDistance (ψ φ : E) : ℝ :=
  (1 / 2) * traceNorm (traceBasis E) (pureStateDifference ψ φ)

/-- The pure-state trace-distance identity stated after Theorem 1.1.
The manuscript writes the inner product in the reverse order, with the same norm. -/
theorem pureStateTraceDistance_eq_sqrt (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    pureStateTraceDistance ψ φ = Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2) := by
  rw [pureStateTraceDistance, traceNorm_pureStateDifference _ ψ φ hψ hφ]
  ring

/-- The distance can be computed as half the trace norm in any Hilbert basis. -/
theorem pureStateTraceDistance_eq_half_traceNorm (b : HilbertBasis ι ℂ E)
    (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    pureStateTraceDistance ψ φ = (1 / 2) * traceNorm b (pureStateDifference ψ φ) := by
  rw [pureStateTraceDistance_eq_sqrt ψ φ hψ hφ,
    traceNorm_pureStateDifference b ψ φ hψ hφ]
  ring

/-- A nonnegative trace-distance threshold is exactly the manuscript's
squared-overlap promise, with no finite-dimensional hypothesis. -/
theorem le_pureStateTraceDistance_iff (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ε ≤ pureStateTraceDistance ψ φ ↔ ‖inner ℂ ψ φ‖ ^ 2 ≤ 1 - ε ^ 2 := by
  rw [pureStateTraceDistance_eq_sqrt ψ φ hψ hφ]
  have hs := Real.sq_sqrt (overlap_deficit_nonneg ψ φ hψ hφ)
  have hn := Real.sqrt_nonneg (1 - ‖inner ℂ ψ φ‖ ^ 2)
  constructor <;> intro h <;> nlinarith

end
end GaussianTesting
