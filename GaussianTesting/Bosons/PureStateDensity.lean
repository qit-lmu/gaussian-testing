module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.DensityPure
public import GaussianTesting.Bosons.PartialTrace
public import GaussianTesting.GradientFlow.FubiniStudy

@[expose] public section

/-!
# Unit vectors, rays, and pure density operators

The manuscript identifies a pure state with its rank-one density operator,
and its unit vector is unique up to phase. These interfaces use the existing
basis-independent density criterion; they are supporting density results in
the bosonic preliminaries.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [completeE : CompleteSpace E]
variable {ι : Type*}

omit completeE in
/-- The trace of a rank-one positive operator is the squared norm of its vector. -/
theorem positiveTrace_rankOne (b : HilbertBasis ι ℂ E) (x : E) :
    positiveTrace b (InnerProductSpace.rankOne ℂ x x) = ‖x‖ ^ 2 := by
  have h : HasSum (fun i => inner ℂ (b i) (InnerProductSpace.rankOne ℂ x x (b i)))
      (inner ℂ x x) := by
    simpa only [InnerProductSpace.rankOne_apply, inner_smul_right, mul_comm] using
      b.hasSum_inner_mul_inner x x
  simpa [positiveTrace, Complex.reCLM_apply, inner_self_eq_norm_sq_to_K,
    pow_two, Complex.mul_re] using
    (Complex.reCLM.hasSum h).tsum_eq

omit completeE in
/-- Every rank-one positive operator is trace class. -/
theorem isPositiveTraceClass_rankOne (b : HilbertBasis ι ℂ E) (x : E) :
    IsPositiveTraceClass b (InnerProductSpace.rankOne ℂ x x) := by
  have h : HasSum (fun i => inner ℂ (b i) (InnerProductSpace.rankOne ℂ x x (b i)))
      (inner ℂ x x) := by
    simpa only [InnerProductSpace.rankOne_apply, inner_smul_right, mul_comm] using
      b.hasSum_inner_mul_inner x x
  exact ⟨ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (InnerProductSpace.isPositive_rankOne_self x),
    (Complex.reCLM.hasSum h).summable⟩

omit completeE in
/-- A vector gives a density operator exactly when it is normalized. -/
theorem isDensityOperator_rankOne_iff [CompleteSpace E] {ι : Type*} (b : HilbertBasis ι ℂ E) (x : E) :
    IsDensityOperator b (InnerProductSpace.rankOne ℂ x x) ↔ ‖x‖ = 1 := by
  constructor
  · intro h
    have ht := h.trace_eq_one
    rw [positiveTrace_rankOne] at ht
    nlinarith [norm_nonneg x]
  · intro hx
    exact ⟨isPositiveTraceClass_rankOne b x, by rw [positiveTrace_rankOne, hx, one_pow]⟩

omit completeE in
/-- Two unit vectors define the same pure density operator exactly when they
differ by a scalar phase. -/
theorem rankOne_eq_iff_phase {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    InnerProductSpace.rankOne ℂ x x = InnerProductSpace.rankOne ℂ y y ↔
      ∃ z : ℂ, ‖z‖ = 1 ∧ x = z • y := by
  constructor
  · intro h
    have he := congrArg (fun A : E →L[ℂ] E => A x) h
    simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hx] at he
    refine ⟨inner ℂ y x, ?_, he⟩
    have hn := congrArg norm he
    simpa only [norm_smul, hx, hy, mul_one] using hn.symm
  · rintro ⟨z, hz, rfl⟩
    ext v
    simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul]
    have hzz : (starRingEnd ℂ) z * z = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
      norm_num
    rw [mul_right_comm, hzz, one_mul]

/-- For density operators, norm one is equivalent to a unit-vector projector. -/
theorem IsDensityOperator.norm_eq_one_iff_rankOne {b : HilbertBasis ι ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) :
    ‖ρ‖ = 1 ↔ ∃ x : E, ‖x‖ = 1 ∧ ρ = InnerProductSpace.rankOne ℂ x x := by
  refine ⟨hρ.exists_rankOne_of_norm_eq_one, ?_⟩
  rintro ⟨x, hx, rfl⟩
  simp [InnerProductSpace.norm_rankOne, hx]

/-- A density operator is a projection exactly when it is a unit-vector
projector; the trace-one hypothesis excludes higher-rank projections. -/
theorem IsDensityOperator.idempotent_iff_rankOne {b : HilbertBasis ι ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) :
    ρ * ρ = ρ ↔ ∃ x : E, ‖x‖ = 1 ∧ ρ = InnerProductSpace.rankOne ℂ x x := by
  constructor
  · intro hi
    apply hρ.exists_rankOne_of_norm_eq_one
    have hs : star ρ = ρ := (IsSelfAdjoint.of_nonneg hρ.nonneg).star_eq
    have hn : ‖ρ‖ * ‖ρ‖ = ‖ρ‖ := by
      rw [← CStarRing.norm_star_mul_self, hs, hi]
    have hne : ‖ρ‖ ≠ 0 := by
      intro hz
      have hzero := norm_eq_zero.mp hz
      have ht := hρ.trace_eq_one
      simp [hzero, positiveTrace] at ht
    exact (mul_left_cancel₀ hne (hn.trans (mul_one ‖ρ‖).symm))
  · rintro ⟨x, hx, rfl⟩
    exact InnerProductSpace.isIdempotentElem_rankOne_self hx

/-- The density projector associated with a ray, independent of phase. -/
def rayProjector (q : Projectivization ℂ E) : E →L[ℂ] E :=
  InnerProductSpace.rankOne ℂ (rayUnitRep q) (rayUnitRep q)

theorem isDensityOperator_rayProjector (b : HilbertBasis ι ℂ E)
    (q : Projectivization ℂ E) : IsDensityOperator b (rayProjector q) :=
  (isDensityOperator_rankOne_iff b _).mpr (norm_rayUnitRep q)

omit completeE in
theorem rayProjector_mk [CompleteSpace E] (x : E) (hx : ‖x‖ = 1) (hn : x ≠ 0) :
    rayProjector (Projectivization.mk ℂ x hn) = InnerProductSpace.rankOne ℂ x x := by
  apply (rankOne_eq_iff_phase (norm_rayUnitRep _) hx).mpr
  obtain ⟨z, hz, he⟩ := rayUnitRep_phase x hx hn
  exact ⟨z, hz, he⟩

omit completeE in
/-- Distinct rays give distinct density projectors. -/
theorem rayProjector_injective [CompleteSpace E] : Function.Injective (rayProjector (E := E)) := by
  intro q r h
  obtain ⟨z, hz, he⟩ :=
    (rankOne_eq_iff_phase (norm_rayUnitRep q) (norm_rayUnitRep r)).mp h
  have hm := (Projectivization.mk_eq_mk_iff' ℂ _ _
    (rayUnitRep_ne_zero q) (rayUnitRep_ne_zero r)).mpr ⟨z, he.symm⟩
  simpa only [mk_rayUnitRep] using hm

/-- Every idempotent density operator comes from a unique ray. -/
theorem IsDensityOperator.existsUnique_rayProjector {b : HilbertBasis ι ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) (hi : ρ * ρ = ρ) :
    ∃! q : Projectivization ℂ E, rayProjector q = ρ := by
  obtain ⟨x, hx, rfl⟩ := hρ.idempotent_iff_rankOne.mp hi
  have hn : x ≠ 0 := by intro h; simp [h] at hx
  refine ⟨Projectivization.mk ℂ x hn, rayProjector_mk x hx hn, ?_⟩
  intro q hq
  exact rayProjector_injective (hq.trans (rayProjector_mk x hx hn).symm)

end
end GaussianTesting.HilbertDensity
