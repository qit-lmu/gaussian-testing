module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.HilbertDensity
public import GaussianTesting.Bosons.DensityTensor
public import GaussianTesting.GradientFlow.HilbertTensor

@[expose] public section

/-!
# The signed-swap trace proof of Lemma 6.2

This is the manuscript's argument on arbitrary complex Hilbert spaces. A
tensor-product isometric embedding suffices to interpret the two-copy density
in a physical Hilbert space. The signed-swap trace is `Tr(Jρ²)`; its modulus is
bounded by the purity, which is at most the operator norm for a density operator.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace TensorProduct

set_option maxHeartbeats 1600000

variable {E H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {κ ν ι : Type*}

omit [CompleteSpace E] [CompleteSpace H] in
theorem GramFam.map {g : ι → E} (hg : GramFam g) (A : E →L[ℂ] H) :
    GramFam (fun i => A (g i)) := by
  apply (hg.mul_left (‖A‖ ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro i
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (g i)) 2

theorem gramOp_map (b : HilbertBasis κ ℂ E) (c : HilbertBasis ν ℂ H)
    {g : ι → E} (hg : GramFam g) (A : E →L[ℂ] H) :
    gramOp c (fun i => A (g i)) (hg.map A) =
      (A.comp (gramOp b g hg)).comp A.adjoint := by
  ext x
  have h := (gramOp_hasSum b hg (A.adjoint x)).mapL A
  have hi (i : ι) : inner ℂ (g i) (A.adjoint x) = inner ℂ (A (g i)) x :=
    A.adjoint_inner_right _ _
  have h' : HasSum (fun i => inner ℂ (A (g i)) x • A (g i))
      (A (gramOp b g hg (A.adjoint x))) := by
    simpa only [hi, map_smul] using h
  exact (gramOp_hasSum c (hg.map A) x).unique h'

omit [CompleteSpace E] in
theorem norm_hilbertTmul (x y : E) : ‖hilbertTmul x y‖ = ‖x‖ * ‖y‖ := by
  exact (UniformSpace.Completion.norm_coe (x ⊗ₜ[ℂ] y)).trans
    (TensorProduct.norm_tmul x y)

/-- The basis on the completed tensor square determined by product coordinates. -/
noncomputable def tensorBasis (b : HilbertBasis κ ℂ E) :
    HilbertBasis (κ × κ) ℂ (HilbertSquare E) :=
  .ofRepr (hilbertCoords b.repr b.repr)

omit [CompleteSpace E] in
theorem GramFam.tensor {g : ι → E} (hg : GramFam g) :
    GramFam (fun p : ι × ι => hilbertTmul (g p.1) (g p.2)) := by
  simpa only [GramFam, norm_hilbertTmul, mul_pow] using
    hg.mul_of_nonneg hg (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

omit [CompleteSpace E] in
theorem tensor_gram_mass {g : ι → E} (hg : GramFam g) :
    ∑' p : ι × ι, ‖hilbertTmul (g p.1) (g p.2)‖ ^ 2 =
      (∑' i, ‖g i‖ ^ 2) ^ 2 := by
  simp only [norm_hilbertTmul, mul_pow]
  rw [(hg.mul_of_nonneg hg (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)).tsum_prod]
  simp_rw [tsum_mul_left, tsum_mul_right]
  ring

private theorem repr_gramOp (b : HilbertBasis κ ℂ E) {g : ι → E} (hg : GramFam g)
    (x : E) : b.repr (gramOp b g hg x) =
      GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b) (b.repr x) := by
  have h := DFunLike.congr_fun (inBasis_gramOp b g hg) (b.repr x)
  simpa only [inBasis_apply, b.repr.symm_apply_apply] using h

/-- The Gram tensor family is the actual completed tensor-product operator. -/
theorem gramOp_tensor (b : HilbertBasis κ ℂ E) {g : ι → E} (hg : GramFam g) :
    gramOp (tensorBasis b) (fun p : ι × ι => hilbertTmul (g p.1) (g p.2)) hg.tensor =
      hilbertTensorMap (gramOp b g hg) (gramOp b g hg) := by
  apply hilbertTensor_ext
  intro x y
  apply (hilbertCoords b.repr b.repr).injective
  rw [hilbertTensorMap_tmul, hilbertCoords_tmul]
  change (tensorBasis b).repr
    (gramOp (tensorBasis b) (fun p : ι × ι => hilbertTmul (g p.1) (g p.2))
      hg.tensor (hilbertTmul x y)) = _
  rw [repr_gramOp]
  simp only [tensorBasis, hilbertCoords_tmul]
  change GaussianTesting.gramOp
    (tensorFam (fun i => b.repr (g i)) (fun i => b.repr (g i))) _
    (tpPair (b.repr x) (b.repr y)) = _
  rw [gramOp_tensorFam_tp]
  rw [repr_gramOp, repr_gramOp]

/-- The actual two-copy density operator in an ambient physical Hilbert space. -/
noncomputable def embeddedTensor (T : HilbertSquare E →ₗᵢ[ℂ] H) (ρ : E →L[ℂ] E) :
    H →L[ℂ] H :=
  (T.toContinuousLinearMap.comp (hilbertTensorMap ρ ρ)).comp
    T.toContinuousLinearMap.adjoint

omit [CompleteSpace E] [CompleteSpace H] in
theorem GramFam.embeddedTensor {g : ι → E} (hg : GramFam g)
    (T : HilbertSquare E →ₗᵢ[ℂ] H) :
    GramFam (fun p : ι × ι => T (hilbertTmul (g p.1) (g p.2))) := by
  simpa only [GramFam, T.norm_map] using hg.tensor

theorem embeddedTensor_eq_gramOp (b : HilbertBasis κ ℂ E) (c : HilbertBasis ν ℂ H)
    {g : ι → E} (hg : GramFam g) (T : HilbertSquare E →ₗᵢ[ℂ] H) :
    embeddedTensor T (gramOp b g hg) =
      gramOp c (fun p : ι × ι => T (hilbertTmul (g p.1) (g p.2))) (hg.embeddedTensor T) := by
  rw [embeddedTensor, ← gramOp_tensor b hg]
  exact (gramOp_map (tensorBasis b) c hg.tensor T.toContinuousLinearMap).symm

theorem IsDensityOperator.embeddedTensor {b : HilbertBasis κ ℂ E} {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator b ρ) (c : HilbertBasis ν ℂ H)
    (T : HilbertSquare E →ₗᵢ[ℂ] H) : IsDensityOperator c (embeddedTensor T ρ) := by
  obtain ⟨g, hg, hmass, rfl⟩ := hρ.exists_normalized_gram_representation
  rw [embeddedTensor_eq_gramOp b c hg T]
  apply isDensityOperator_gramOp
  simp only [T.norm_map, tensor_gram_mass hg, hmass, one_pow]

theorem IsPositiveTraceClass.positiveTrace_nonneg {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) : 0 ≤ positiveTrace b ρ := by
  obtain ⟨g, hg, _, hmass⟩ := hρ.exists_gram_representation
  rw [← hmass]
  exact tsum_nonneg (fun _ => sq_nonneg _)

/-- The square of a positive trace-class operator is again positive trace class. -/
theorem IsPositiveTraceClass.square {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ) : IsPositiveTraceClass b (ρ * ρ) :=
  ⟨(IsSelfAdjoint.of_nonneg hρ.nonneg).mul_self_nonneg,
    (Complex.hasSum_re (hρ.mul_hasSum_diagonal ρ b)).summable⟩

/-- For trace-one positive operators, purity is at most operator norm. -/
theorem IsDensityOperator.purity_le_norm {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) :
    positiveTrace b (ρ * ρ) ≤ ‖ρ‖ := by
  calc
    _ = (operatorTrace b (ρ * ρ)).re := by
      rw [hρ.toIsPositiveTraceClass.square.operatorTrace_eq_positiveTrace]
      rfl
    _ ≤ ‖operatorTrace b (ρ * ρ)‖ := Complex.re_le_norm _
    _ ≤ ‖ρ‖ := by
      simpa only [hρ.trace_eq_one, mul_one] using
        hρ.toIsPositiveTraceClass.norm_operatorTrace_mul_le ρ

omit [CompleteSpace E] in
private theorem signed_swap_terms_summable {g : ι → E} (hg : GramFam g)
    (J : E ≃ₗᵢ[ℂ] E) : Summable (fun p : ι × ι =>
      inner ℂ (g p.1) (J (g p.2)) * inner ℂ (g p.2) (g p.1)) := by
  apply Summable.of_norm
  apply (hg.mul_of_nonneg hg (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro p
  rw [norm_mul]
  calc
    _ ≤ (‖g p.1‖ * ‖g p.2‖) * (‖g p.2‖ * ‖g p.1‖) := by
      apply mul_le_mul _ (norm_inner_le_norm _ _) (norm_nonneg _) (by positivity)
      simpa only [J.norm_map] using norm_inner_le_norm (𝕜 := ℂ) (g p.1) (J (g p.2))
    _ = ‖g p.1‖ ^ 2 * ‖g p.2‖ ^ 2 := by ring

/-- The complex signed-swap identity in the manuscript, including the physical
tensor embedding. It is valid for every positive trace-class operator. -/
theorem signedSwap_trace {b : HilbertBasis κ ℂ E} (c : HilbertBasis ν ℂ H)
    {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ)
    (T : HilbertSquare E →ₗᵢ[ℂ] H) (J : E ≃ₗᵢ[ℂ] E) (W : H ≃ₗᵢ[ℂ] H)
    (hW : ∀ x y, W (T (hilbertTmul x y)) = T (hilbertTmul (J y) x)) :
    operatorTrace c (W.toContinuousLinearEquiv.toContinuousLinearMap * embeddedTensor T ρ) =
      operatorTrace b (J.toContinuousLinearEquiv.toContinuousLinearMap * (ρ * ρ)) := by
  obtain ⟨g, hg, rfl, _⟩ := hρ.exists_gram_representation
  rw [embeddedTensor_eq_gramOp b c hg T, operatorTrace_mul_gramOp,
    ← mul_assoc, operatorTrace_mul_gramOp]
  have hrow (i : κ) : HasSum
      (fun j => inner ℂ (g i) (J (g j)) * inner ℂ (g j) (g i))
      (inner ℂ (g i) (J (gramOp b g hg (g i)))) := by
    have h := ((gramOp_hasSum b hg (g i)).mapL
      J.toContinuousLinearEquiv.toContinuousLinearMap).mapL (innerSL ℂ (g i))
    simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      innerSL_apply_apply, map_smul, inner_smul_right, smul_eq_mul, mul_comm] using h
  change (∑' i : κ × κ,
    inner ℂ (T (hilbertTmul (g i.1) (g i.2))) (W (T (hilbertTmul (g i.1) (g i.2))))) =
      ∑' i, inner ℂ (g i) (J (gramOp b g hg (g i)))
  simp only [hW, T.inner_map_map, inner_hilbertTmul]
  rw [(signed_swap_terms_summable hg J).tsum_prod]
  exact tsum_congr (fun i => (hrow i).tsum_eq)

/-- The modulus of the signed-swap trace is at most purity. -/
theorem signedSwap_trace_norm_le_purity {b : HilbertBasis κ ℂ E}
    (c : HilbertBasis ν ℂ H) {ρ : E →L[ℂ] E} (hρ : IsPositiveTraceClass b ρ)
    (T : HilbertSquare E →ₗᵢ[ℂ] H) (J : E ≃ₗᵢ[ℂ] E) (W : H ≃ₗᵢ[ℂ] H)
    (hW : ∀ x y, W (T (hilbertTmul x y)) = T (hilbertTmul (J y) x)) :
    ‖operatorTrace c (W.toContinuousLinearEquiv.toContinuousLinearMap * embeddedTensor T ρ)‖ ≤
      positiveTrace b (ρ * ρ) := by
  rw [signedSwap_trace c hρ T J W hW]
  exact (hρ.square.norm_operatorTrace_mul_le J.toContinuousLinearEquiv.toContinuousLinearMap).trans
    (mul_le_of_le_one_left hρ.square.positiveTrace_nonneg
      J.toLinearIsometry.norm_toContinuousLinearMap_le)

private theorem expectation_summable (b : HilbertBasis κ ℂ E) {g : ι → E}
    (hg : GramFam g) (A : E →L[ℂ] E) : Summable (fun i => inner ℂ (g i) (A (g i))) := by
  simpa only [inBasis_apply, b.repr.symm_apply_apply, b.repr.inner_map_map] using
    GaussianTesting.complexTrPair_summable (hg.inBasis b) (inBasis b A)

omit [CompleteSpace H] in
/-- A unitary that fixes the projection range has real expectation at least
twice the projection expectation minus the squared norm. -/
theorem projection_fixed_unitary_lower (P : H →L[ℂ] H) (W : H ≃ₗᵢ[ℂ] H)
    (hPsymm : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hPidem : ∀ x, P (P x) = P x) (hWP : ∀ x, W (P x) = P x) (x : H) :
    2 * (inner ℂ x (P x)).re - ‖x‖ ^ 2 ≤ (inner ℂ x (W x)).re := by
  have re_self (y : H) : (inner ℂ y y).re = ‖y‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  have hproj : inner ℂ x (P x) = inner ℂ (P x) (P x) := by
    rw [hPsymm, hPidem]
  let p := P x
  let r := x - p
  have hpr : inner ℂ p r = 0 := by
    simp only [r, inner_sub_right]
    have hs := hPsymm x x
    rw [hproj] at hs
    exact sub_eq_zero.mpr hs
  have hrp : inner ℂ r p = 0 := by rw [← inner_conj_symm, hpr]; simp
  have hwp : W p = p := hWP x
  have hpwr : inner ℂ p (W r) = 0 := by
    rw [← hwp, W.inner_map_map, hpr]
  have hx : x = p + r := by dsimp [r]; abel
  have he : inner ℂ x (W x) = inner ℂ p p + inner ℂ r (W r) := by
    conv_lhs => rw [hx, map_add, inner_add_left, inner_add_right, inner_add_right]
    rw [hwp, hpwr, hrp]
    ring
  have hn : ‖x‖ ^ 2 = ‖p‖ ^ 2 + ‖r‖ ^ 2 := by
    have hh : inner ℂ x x = inner ℂ p p + inner ℂ r r := by
      conv_lhs => rw [hx, inner_add_left, inner_add_right, inner_add_right]
      rw [hpr, hrp]
      ring
    have h := congrArg Complex.re hh
    simpa only [Complex.add_re, re_self] using h
  have hb : -‖r‖ ^ 2 ≤ (inner ℂ r (W r)).re := by
    have h₁ := Complex.abs_re_le_norm (inner ℂ r (W r))
    have h₂ := norm_inner_le_norm (𝕜 := ℂ) r (W r)
    rw [W.norm_map] at h₂
    nlinarith [neg_le_abs (inner ℂ r (W r)).re]
  rw [he, Complex.add_re, hproj]
  simp only [re_self]
  change 2 * ‖p‖ ^ 2 - ‖x‖ ^ 2 ≤ ‖p‖ ^ 2 + _
  linarith

/-- The projection-versus-unitary bound after taking a density-operator trace. -/
theorem projection_fixed_unitary_trace_lower {c : HilbertBasis ν ℂ H}
    {σ : H →L[ℂ] H} (hσ : IsDensityOperator c σ) (P : H →L[ℂ] H)
    (W : H ≃ₗᵢ[ℂ] H)
    (hPsymm : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hPidem : ∀ x, P (P x) = P x) (hWP : ∀ x, W (P x) = P x) :
    2 * (operatorTrace c (P * σ)).re - 1 ≤
      (operatorTrace c (W.toContinuousLinearEquiv.toContinuousLinearMap * σ)).re := by
  obtain ⟨g, hg, hmass, rfl⟩ := hσ.exists_normalized_gram_representation
  have hP := Complex.hasSum_re (expectation_summable c hg P).hasSum
  have hW := Complex.hasSum_re
    (expectation_summable c hg W.toContinuousLinearEquiv.toContinuousLinearMap).hasSum
  have h := ((hP.summable.mul_left 2).sub hg).tsum_le_tsum
    (fun i => projection_fixed_unitary_lower P W hPsymm hPidem hWP (g i)) hW.summable
  rw [Summable.tsum_sub (hP.summable.mul_left 2) hg, tsum_mul_left, hmass] at h
  rw [operatorTrace_mul_gramOp, operatorTrace_mul_gramOp, ← hP.tsum_eq, ← hW.tsum_eq]
  exact h

/-- **Lemma 6.2, signed-swap form.** The manuscript's full trace argument for
any tensor-product isometric embedding and the corresponding acceptance projection. -/
theorem purity_of_signedSwap {b : HilbertBasis κ ℂ E} (c : HilbertBasis ν ℂ H)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ)
    (T : HilbertSquare E →ₗᵢ[ℂ] H) (J : E ≃ₗᵢ[ℂ] E) (W : H ≃ₗᵢ[ℂ] H)
    (hW : ∀ x y, W (T (hilbertTmul x y)) = T (hilbertTmul (J y) x))
    (P : H →L[ℂ] H)
    (hPsymm : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hPidem : ∀ x, P (P x) = P x) (hWP : ∀ x, W (P x) = P x)
    {τ : ℝ} (hp : 1 - τ ≤ (operatorTrace c (P * embeddedTensor T ρ)).re) :
    1 - 2 * τ ≤ ‖ρ‖ := by
  have hl := projection_fixed_unitary_trace_lower (hρ.embeddedTensor c T) P W
    hPsymm hPidem hWP
  have hu := signedSwap_trace_norm_le_purity c hρ.toIsPositiveTraceClass T J W hW
  have hr := Complex.re_le_norm
    (operatorTrace c (W.toContinuousLinearEquiv.toContinuousLinearMap * embeddedTensor T ρ))
  have hpurity := hρ.purity_le_norm
  linarith

end GaussianTesting.HilbertDensity
