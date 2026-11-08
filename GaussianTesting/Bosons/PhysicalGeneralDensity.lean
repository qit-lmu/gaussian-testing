module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.HilbertDensity
public import GaussianTesting.Bosons.PhysicalMeanZero
public import GaussianTesting.Bosons.SchrodingerPurity

@[expose] public section

/-!
# The density-operator reduction in Theorem 6.7

These are the density-operator steps of the manuscript's quantitative purity
argument. A density operator has a unit eigenvector at its operator norm,
and positivity of the residual bounds both single-copy expectations and
two-copy rejection. Applied to the actual reduced state, this gives the
mean-zero acceptance bound for the top eigenstate. The final numerical
estimate gives reduced-state weight `1 - 12τ` after the mean-zero fidelity
bound has supplied an appropriate state; it does not assert Theorem 6.7
without that separate input and the subsequent Gaussian transport.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace

noncomputable section

variable {E κ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

omit [CompleteSpace E] in
/-- Trace one excludes the zero operator. -/
theorem IsDensityOperator.ne_zero {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) : ρ ≠ 0 := by
  intro hzero
  have htrace := hρ.trace_eq_one
  simp [positiveTrace, hzero] at htrace

/-- The density bound used together with Lemma 6.2 in Theorem 6.7. -/
theorem IsDensityOperator.norm_le_one {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) : ‖ρ‖ ≤ 1 := by
  obtain ⟨g, hg, hmass, rfl⟩ := hρ.exists_normalized_gram_representation
  have h := GaussianTesting.gramOp_norm_le (hg.inBasis b)
  rw [← inBasis_gramOp b g hg, inBasis_norm] at h
  simpa only [b.repr.norm_map, hmass] using h

/-- The manuscript's top eigenstate of a nonzero physical density operator. -/
theorem IsDensityOperator.exists_top_eigenvector {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) :
    ∃ ξ : E, ‖ξ‖ = 1 ∧ ρ ξ = (‖ρ‖ : ℂ) • ξ := by
  obtain ⟨g, hg, _, hrep⟩ := hρ.exists_normalized_gram_representation
  have heq : GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b) =
      inBasis b ρ := by rw [← inBasis_gramOp b g hg, hrep]
  have hn : GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b) ≠ 0 := by
    rw [heq]
    exact fun h => hρ.ne_zero ((inBasis b).injective (h.trans (map_zero (inBasis b)).symm))
  obtain ⟨ξ, hξ, heig⟩ := GaussianTesting.exists_top_eigenvector (hg.inBasis b) hn
  refine ⟨b.repr.symm ξ, by simpa only [b.repr.symm.norm_map] using hξ, ?_⟩
  apply b.repr.injective
  rw [heq, inBasis_norm] at heig
  simpa only [inBasis_apply, map_smul, b.repr.apply_symm_apply] using heig

/-- Positivity of the residual density gives the eigenstate contribution
to every expectation, as used after symplectic transport in Theorem 6.7. -/
theorem IsDensityOperator.eigenstate_weight_le {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ)
    {ξ : E} (hξ : ‖ξ‖ = 1) {lam : ℝ} (heig : ρ ξ = (lam : ℂ) • ξ) (φ : E) :
    lam * ‖inner ℂ ξ φ‖ ^ 2 ≤ (inner ℂ φ (ρ φ)).re := by
  obtain ⟨g, hg, _, hrep⟩ := hρ.exists_normalized_gram_representation
  have hgc : GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b) =
      inBasis b ρ := by rw [← inBasis_gramOp b g hg, hrep]
  have he : GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b)
      (b.repr ξ) = (lam : ℂ) • b.repr ξ := by
    rw [hgc, inBasis_apply, b.repr.symm_apply_apply, heig, map_smul]
  have hn : ‖b.repr ξ‖ = 1 := (b.repr.norm_map ξ).trans hξ
  have hs := GaussianTesting.gramOp_eq_top_add_residual (hg.inBasis b) hn he (b.repr φ)
  have hr := GaussianTesting.gramOp_nonneg
    (GaussianTesting.residualFam_gramFam (hg.inBasis b) (b.repr ξ)) (b.repr φ)
  have hi := congrArg (fun v => (inner ℂ (b.repr φ) v).re) hs
  rw [hgc, inBasis_apply, b.repr.symm_apply_apply, b.repr.inner_map_map,
    inner_add_right, inner_smul_right, inner_smul_right, Complex.add_re] at hi
  rw [b.repr.inner_map_map, b.repr.inner_map_map,
    ← inner_conj_symm φ ξ, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hi
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at hi
  linarith

/-- The residual positivity estimate on two copies used in Theorem 6.7.
It applies to every positive observable, in particular to `I - P₀`. -/
theorem IsDensityOperator.eigenstate_tensor_weight_le {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ)
    {ξ : E} (hξ : ‖ξ‖ = 1) {lam : ℝ} (hlam : 0 ≤ lam)
    (heig : ρ ξ = (lam : ℂ) • ξ) (B : HilbertSquare E →L[ℂ] HilbertSquare E)
    (hB : ∀ x, 0 ≤ (inner ℂ x (B x)).re) :
    lam ^ 2 * (inner ℂ (hilbertTmul ξ ξ) (B (hilbertTmul ξ ξ))).re ≤
      (operatorTrace (tensorBasis b) (B * hilbertTensorMap ρ ρ)).re := by
  obtain ⟨g, hg, _, hrep⟩ := hρ.exists_normalized_gram_representation
  let Bc := inBasis (tensorBasis b) B
  have hgc : GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b) =
      inBasis b ρ := by rw [← inBasis_gramOp b g hg, hrep]
  have he : GaussianTesting.gramOp (fun i => b.repr (g i)) (hg.inBasis b)
      (b.repr ξ) = (lam : ℂ) • b.repr ξ := by
    rw [hgc, inBasis_apply, b.repr.symm_apply_apply, heig, map_smul]
  have hBc (x : L2 (κ × κ)) : 0 ≤ (inner ℂ x (Bc x)).re := by
    have hi := (tensorBasis b).repr.inner_map_map ((tensorBasis b).repr.symm x)
      (B ((tensorBasis b).repr.symm x))
    rw [(tensorBasis b).repr.apply_symm_apply] at hi
    change 0 ≤ (inner ℂ x ((tensorBasis b).repr (B ((tensorBasis b).repr.symm x)))).re
    rw [hi]
    exact hB _
  have hd := GaussianTesting.trPair_tensor_ge (hg.inBasis b) hBc
    ((b.repr.norm_map ξ).trans hξ) hlam he
  have htrace : (operatorTrace (tensorBasis b) (B * hilbertTensorMap ρ ρ)).re =
      GaussianTesting.trPair Bc
        (GaussianTesting.tensorFam (fun i => b.repr (g i)) (fun i => b.repr (g i))) := by
    rw [← hrep, ← gramOp_tensor b hg, operatorTrace_mul_gramOp,
      ← GaussianTesting.complexTrPair_re (GaussianTesting.tensorFam_gramFam (hg.inBasis b) (hg.inBasis b)) Bc]
    congr 1
    apply tsum_congr
    intro p
    have hv : GaussianTesting.tpPair (b.repr (g p.1)) (b.repr (g p.2)) =
        (tensorBasis b).repr (hilbertTmul (g p.1) (g p.2)) :=
      (hilbertCoords_tmul _ _ _ _).symm
    change inner ℂ (hilbertTmul (g p.1) (g p.2)) (B (hilbertTmul (g p.1) (g p.2))) =
      inner ℂ (GaussianTesting.tpPair (b.repr (g p.1)) (b.repr (g p.2)))
        (Bc (GaussianTesting.tpPair (b.repr (g p.1)) (b.repr (g p.2))))
    rw [hv]
    simp only [Bc, inBasis_apply, (tensorBasis b).repr.symm_apply_apply,
      (tensorBasis b).repr.inner_map_map]
  rw [htrace]
  have hv : GaussianTesting.tpPair (b.repr ξ) (b.repr ξ) =
      (tensorBasis b).repr (hilbertTmul ξ ξ) := (hilbertCoords_tmul _ _ _ _).symm
  rw [hv] at hd
  simpa only [Bc, inBasis_apply, (tensorBasis b).repr.symm_apply_apply,
    (tensorBasis b).repr.inner_map_map] using hd

private theorem density_tensor {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) :
    IsDensityOperator (tensorBasis b) (hilbertTensorMap ρ ρ) := by
  obtain ⟨g, hg, hmass, rfl⟩ := hρ.exists_normalized_gram_representation
  rw [← gramOp_tensor b hg]
  exact isDensityOperator_gramOp _ hg.tensor (by rw [tensor_gram_mass hg, hmass, one_pow])

private theorem trace_defect {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ) (P : E →L[ℂ] E) :
    (operatorTrace b ((1 - P) * ρ)).re = 1 - (operatorTrace b (P * ρ)).re := by
  have hs := hρ.toIsPositiveTraceClass.mul_hasSum_diagonal 1 b
  have hp := hρ.toIsPositiveTraceClass.mul_hasSum_diagonal P b
  simp only [one_mul] at hs
  have ht : operatorTrace b ((1 - P) * ρ) =
      operatorTrace b ρ - operatorTrace b (P * ρ) := by
    simp only [operatorTrace, sub_mul, one_mul, sub_apply, inner_sub_right]
    exact hs.summable.tsum_sub hp.summable
  rw [ht, Complex.sub_re, hρ.toIsPositiveTraceClass.operatorTrace_eq_positiveTrace,
    hρ.trace_eq_one, Complex.ofReal_one, Complex.one_re]

omit [CompleteSpace E] in
private theorem projection_defect_nonneg (P : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hi : ∀ x, P (P x) = P x) (x : E) :
    0 ≤ (inner ℂ x ((1 - P) x)).re := by
  have hxp : inner ℂ x (P x) = inner ℂ (P x) (P x) := by rw [hs, hi]
  have hpx : inner ℂ (P x) x = inner ℂ x (P x) := hs x x
  have he : inner ℂ x ((1 - P) x) = inner ℂ (x - P x) (x - P x) := by
    simp only [sub_apply, one_apply_eq_self, inner_sub_right, inner_sub_left]
    rw [hpx, hxp]
    ring
  rw [he]
  exact inner_self_nonneg (𝕜 := ℂ) (x := x - P x)

/-- Subtracting the tensor estimate from the trace-one identity gives the
manuscript's rejection bound `lam² (1 - p₀(ξ)) ≤ 1 - Tr(P₀ ρ⊗²)`. -/
theorem IsDensityOperator.eigenstate_rejection_le {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ)
    {ξ : E} (hξ : ‖ξ‖ = 1) {lam : ℝ} (hlam : 0 ≤ lam)
    (heig : ρ ξ = (lam : ℂ) • ξ) (P : HilbertSquare E →L[ℂ] HilbertSquare E)
    (hs : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hi : ∀ x, P (P x) = P x) :
    lam ^ 2 * (1 - (inner ℂ (hilbertTmul ξ ξ) (P (hilbertTmul ξ ξ))).re) ≤
      1 - (operatorTrace (tensorBasis b) (P * hilbertTensorMap ρ ρ)).re := by
  have hd := hρ.eigenstate_tensor_weight_le hξ hlam heig (1 - P)
    (projection_defect_nonneg P hs hi)
  rw [trace_defect (density_tensor hρ)] at hd
  simp only [sub_apply, one_apply_eq_self, inner_sub_right, Complex.sub_re,
    inner_self_eq_norm_sq_to_K, norm_hilbertTmul, hξ, one_mul] at hd
  norm_num at hd
  exact hd

/-- The numerical step after the mean-zero fidelity bound in Theorem 6.7:
an overlap of `1 - 8τ/lam²` yields reduced-state weight at least `1 - 12τ`. -/
theorem IsDensityOperator.eigenstate_weight_ge_of_overlap {b : HilbertBasis κ ℂ E}
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator b ρ)
    {ξ φ : E} (hξ : ‖ξ‖ = 1) (heig : ρ ξ = (‖ρ‖ : ℂ) • ξ)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 48) (hlower : 1 - 2 * τ ≤ ‖ρ‖)
    (hoverlap : 1 - 8 * (τ / ‖ρ‖ ^ 2) ≤ ‖inner ℂ ξ φ‖ ^ 2) :
    1 - 12 * τ ≤ (inner ℂ φ (ρ φ)).re := by
  let lam := ‖ρ‖
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hw := hρ.eigenstate_weight_le hξ heig φ
  have hweight : lam * (1 - 8 * (τ / lam ^ 2)) ≤ (inner ℂ φ (ρ φ)).re :=
    (mul_le_mul_of_nonneg_left hoverlap hlam.le).trans hw
  have hnum : 1 - 12 * τ ≤ lam * (1 - 8 * (τ / lam ^ 2)) := by
    apply (mul_le_mul_iff_left₀ hlam).mp
    have hid : lam * (lam * (1 - 8 * (τ / lam ^ 2))) = lam ^ 2 - 8 * τ := by
      field_simp
    rw [mul_comm (lam * (1 - 8 * (τ / lam ^ 2))) lam, hid]
    have hx : 0 ≤ lam - (1 - 2 * τ) := by dsimp [lam]; linarith
    have hy : 0 ≤ lam - (1 - 2 * τ) + 1 + 8 * τ := by linarith
    nlinarith [mul_nonneg hx hy, mul_nonneg hτ0 (show 0 ≤ 1 - 10 * τ by linarith)]
  exact hnum.trans hweight

end
end GaussianTesting.HilbertDensity

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The top-eigenstate reduction in the first half of Theorem 6.7, for the
actual four-copy test and its physical reduced state. The mean-zero fidelity
bound is subsequently applied to this `ξ`, exactly as in the manuscript. -/
theorem schrodingerReducedState_top_eigenstate {m : ℕ} {κ ν : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ψ : WaveSpace m} (hψ : ‖ψ‖ = 1) {τ : ℝ} (hτ : τ ≤ 1 / 48)
    (hp : 1 - τ ≤ schrodingerFourCopyAcceptance ψ) :
    let ρ := schrodingerReducedState b ψ
    ∃ ξ : WaveSpace m, ‖ξ‖ = 1 ∧ ρ ξ = (‖ρ‖ : ℂ) • ξ ∧
      1 - 2 * τ ≤ ‖ρ‖ ∧ ‖ρ‖ ≤ 1 ∧
      1 - τ / ‖ρ‖ ^ 2 ≤ schrodingerMeanZeroAcceptance ξ ∧
      ∀ φ : WaveSpace m, ‖ρ‖ * ‖inner ℂ ξ φ‖ ^ 2 ≤ (inner ℂ φ (ρ φ)).re := by
  let ρ := schrodingerReducedState b ψ
  have hρ := schrodingerReducedState_isDensityOperator b ψ hψ
  have hpa : 1 - τ ≤ (HilbertDensity.operatorTrace c
      (schrodingerDensityTensor m ρ * schrodingerP0 m)).re := by
    have hcomm := (hρ.embeddedTensor c (waveTensor m)).toIsPositiveTraceClass.operatorTrace_mul_comm
      (schrodingerP0 m)
    change HilbertDensity.operatorTrace c (schrodingerP0 m * schrodingerDensityTensor m ρ) =
      HilbertDensity.operatorTrace c (schrodingerDensityTensor m ρ * schrodingerP0 m) at hcomm
    rw [← hcomm]
    exact (schrodingerFourCopyAcceptance_eq_reducedTrace b c ψ) ▸ hp
  have hlower : 1 - 2 * τ ≤ ‖ρ‖ := purity_schrodinger c hρ hpa
  have hpos : 0 < ‖ρ‖ := by linarith
  obtain ⟨ξ, hξ, heig⟩ := hρ.exists_top_eigenvector
  refine ⟨ξ, hξ, heig, hlower, hρ.norm_le_one, ?_, hρ.eigenstate_weight_le hξ heig⟩
  have hd := hρ.eigenstate_rejection_le hξ (norm_nonneg ρ) heig (schrodingerTensorP0 m)
    (schrodingerTensorP0_symmetric m) (schrodingerTensorP0_idempotent m)
  have hacc : schrodingerFourCopyAcceptance ψ =
      (HilbertDensity.operatorTrace (HilbertDensity.tensorBasis b)
        (schrodingerTensorP0 m * hilbertTensorMap ρ ρ)).re :=
    fourCopyAcceptance_eq_reducedTrace b (schrodingerTensorRotation m (Real.pi / 4))
      (schrodingerTensorP0 m) ψ
  change ‖ρ‖ ^ 2 * (1 - schrodingerMeanZeroAcceptance ξ) ≤ _ at hd
  rw [← hacc] at hd
  have hrej : ‖ρ‖ ^ 2 * (1 - schrodingerMeanZeroAcceptance ξ) ≤ τ := by linarith
  have hdiv : 1 - schrodingerMeanZeroAcceptance ξ ≤ τ / ‖ρ‖ ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hpos)).mpr (by nlinarith [hrej])
  linarith

end
end GaussianTesting
