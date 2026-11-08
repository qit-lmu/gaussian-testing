module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.ThreeCopy
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

/-!
# Gram-family operators on ℓ²: elementary mixed-state calculus

Reduced density operators in the four-copy bosonic test are *Gram operators*
`ρ = ∑_k |g k⟩⟨g k|` of ℓ²-summable families `g : ι → L2 κ`
(`∑_k ‖g k‖² < ∞`) — concretely, the columns of a purification.  All traces
are explicit `tsum`s over the family; no abstract trace-class theory is used.

## Contents

* `gramOp g hg` — the bounded operator `x ↦ ∑'_k ⟪g k, x⟫ • g k`; symmetry,
  positivity, norm bound.
* `trPair B g` — the trace pairing `∑'_k re ⟪g k, B (g k)⟫`; nonnegativity for
  positive `B`, family-independence (`trPair_congr`: it only depends on
  `gramOp g`), the total trace `trPair 1 g = ∑' ‖g k‖²`.
* `gramOp_isCompactOperator` — Gram operators are compact (norm limits of
  finite sub-family truncations).
* `exists_top_eigenvector` — a nonzero Gram operator has a unit eigenvector
  with eigenvalue `‖gramOp g hg‖` (compact spectral theory: nonzero spectral
  points of compact operators are eigenvalues, and the spectral radius of a
  self-adjoint operator equals its norm).
* `trPair_gramOp_le` — `tr ρ² ≤ ‖ρ‖ · tr ρ`.
* `residualFam` — the explicit Gram family of `ρ − λ |ξ⟩⟨ξ|` for a top
  eigenpair: columns `g k − ⟪ξ, g k⟫ • ξ`.
* `tpPair`, `tensorFam` — elementary tensors `L2 κ → L2 κ' → L2 (κ × κ')` and
  product families, with `gramOp`/`trPair` compatibility; the dominance
  inequality `λ² · re ⟪ξ⊗ξ, B (ξ⊗ξ)⟫ ≤ trPair B (tensorFam g g)` for
  positive `B`.
-/

set_option maxHeartbeats 1600000

namespace GaussianTesting

open Complex ENNReal
open scoped ComplexConjugate Topology NNReal

local notation "⟪" x ", " y "⟫_ℂ" => inner ℂ x y

variable {ι κ κ' : Type*}

/-! ### Elementary tensors on two factors -/

/-- Elementary tensor of two ℓ² vectors on the product index. -/
noncomputable def tpPair (f : L2 κ) (g : L2 κ') : L2 (κ × κ') := by
  refine ⟨fun p => f p.1 * g p.2, mem_of_summable_normSq ?_⟩
  have h := (summable_normSq f).mul_of_nonneg (summable_normSq g)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  simpa only [norm_mul, mul_pow] using h

@[simp] lemma tpPair_apply (f : L2 κ) (g : L2 κ') (p : κ × κ') :
    tpPair f g p = f p.1 * g p.2 := rfl

lemma inner_tpPair (f f' : L2 κ) (g g' : L2 κ') :
    ⟪tpPair f g, tpPair f' g'⟫_ℂ = ⟪f, f'⟫_ℂ * ⟪g, g'⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [tpPair_apply, RCLike.inner_apply, map_mul]
  have hf := (lp.summable_inner (𝕜 := ℂ) f f').norm
  have hg := (lp.summable_inner (𝕜 := ℂ) g g').norm
  simpa only [RCLike.inner_apply, mul_mul_mul_comm] using
    (tsum_mul_tsum_of_summable_norm hf hg).symm

lemma norm_tpPair (f : L2 κ) (g : L2 κ') : ‖tpPair f g‖ = ‖f‖ * ‖g‖ := by
  have h := congrArg Complex.re (inner_tpPair f f g g)
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul] at h
  change ‖tpPair f g‖ ^ 2 = ‖f‖ ^ 2 * ‖g‖ ^ 2 at h
  have hn := norm_nonneg (tpPair f g)
  have hf := norm_nonneg f
  have hg := norm_nonneg g
  nlinarith [mul_nonneg hf hg]

/-! ### Gram families and their operators -/

/-- An ℓ²-summable family of vectors. -/
def GramFam (g : ι → L2 κ) : Prop := Summable (fun k => ‖g k‖ ^ 2)

private lemma coeff_norm_summable {g : ι → L2 κ} (hg : GramFam g) (x : L2 κ) :
    Summable (fun k => ‖⟪g k, x⟫_ℂ • g k‖) := by
  apply (hg.mul_right ‖x‖).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  rw [norm_smul]
  calc
    ‖⟪g k, x⟫_ℂ‖ * ‖g k‖ ≤ (‖g k‖ * ‖x‖) * ‖g k‖ :=
      mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = ‖g k‖ ^ 2 * ‖x‖ := by ring

lemma GramFam.summable_coeff {g : ι → L2 κ} (hg : GramFam g) (x : L2 κ) :
    Summable (fun k => ⟪g k, x⟫_ℂ • g k) := by
  exact (coeff_norm_summable hg x).of_norm

/-- The Gram operator `∑'_k |g k⟩⟨g k|` of an ℓ²-summable family. -/
noncomputable def gramOp (g : ι → L2 κ) (hg : GramFam g) : L2 κ →L[ℂ] L2 κ :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' k, ⟪g k, x⟫_ℂ • g k
      map_add' := by
        intro x y
        simp only [inner_add_right, add_smul]
        exact (hg.summable_coeff x).tsum_add (hg.summable_coeff y)
      map_smul' := by
        intro c x
        simp only [inner_smul_right, mul_smul, RingHom.id_apply]
        exact (hg.summable_coeff x).tsum_const_smul c }
    (∑' k, ‖g k‖ ^ 2)
    (by
      intro x
      calc
        ‖∑' k, ⟪g k, x⟫_ℂ • g k‖ ≤ ∑' k, ‖⟪g k, x⟫_ℂ • g k‖ :=
          norm_tsum_le_tsum_norm (coeff_norm_summable hg x)
        _ ≤ ∑' k, ‖g k‖ ^ 2 * ‖x‖ := by
          apply Summable.tsum_le_tsum _ (coeff_norm_summable hg x) (hg.mul_right ‖x‖)
          intro k
          rw [norm_smul]
          calc
            _ ≤ (‖g k‖ * ‖x‖) * ‖g k‖ :=
              mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
            _ = _ := by ring
        _ = (∑' k, ‖g k‖ ^ 2) * ‖x‖ := tsum_mul_right)

lemma gramOp_apply {g : ι → L2 κ} (hg : GramFam g) (x : L2 κ) :
    gramOp g hg x = ∑' k, ⟪g k, x⟫_ℂ • g k := rfl

lemma inner_gramOp {g : ι → L2 κ} (hg : GramFam g) (x y : L2 κ) :
    ⟪x, gramOp g hg y⟫_ℂ = ∑' k, ⟪x, g k⟫_ℂ * ⟪g k, y⟫_ℂ := by
  simpa only [gramOp_apply, innerSL_apply_apply, inner_smul_right, mul_comm] using
    ((hg.summable_coeff y).hasSum.mapL (innerSL ℂ x)).tsum_eq.symm

lemma gramOp_symmetric {g : ι → L2 κ} (hg : GramFam g) (x y : L2 κ) :
    ⟪gramOp g hg x, y⟫_ℂ = ⟪x, gramOp g hg y⟫_ℂ := by
  rw [← inner_conj_symm (gramOp g hg x) y, inner_gramOp hg, inner_gramOp hg,
    Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp only [map_mul, inner_conj_symm]
  ring

lemma inner_gramOp_self {g : ι → L2 κ} (hg : GramFam g) (x : L2 κ) :
    ⟪x, gramOp g hg x⟫_ℂ = ((∑' k, ‖⟪g k, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_gramOp hg, Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  rw [← inner_conj_symm x (g k), mul_comm, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq]

lemma gramOp_nonneg {g : ι → L2 κ} (hg : GramFam g) (x : L2 κ) :
    0 ≤ (⟪x, gramOp g hg x⟫_ℂ).re := by
  rw [inner_gramOp_self hg, Complex.ofReal_re]
  exact tsum_nonneg (fun _ => sq_nonneg _)

lemma gramOp_norm_le {g : ι → L2 κ} (hg : GramFam g) :
    ‖gramOp g hg‖ ≤ ∑' k, ‖g k‖ ^ 2 := by
  exact LinearMap.mkContinuous_norm_le _ (tsum_nonneg (fun _ => sq_nonneg _)) _

/-- Quadratic-form dominance transfers to the operator norm:
`⟪x, ρ x⟫ ≤ ‖ρ‖ ‖x‖²` (special case of Cauchy–Schwarz + symmetry, stated for
convenience). -/
lemma inner_gramOp_le_norm {g : ι → L2 κ} (hg : GramFam g) (x : L2 κ) :
    (⟪x, gramOp g hg x⟫_ℂ).re ≤ ‖gramOp g hg‖ * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖⟪x, gramOp g hg x⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖gramOp g hg x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖gramOp g hg‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((gramOp g hg).le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

/-! ### The trace pairing -/

/-- Trace pairing of a bounded operator against a Gram family:
`tr[B ∑|g⟩⟨g|]` as an explicit sum. -/
noncomputable def trPair (B : L2 κ →L[ℂ] L2 κ) (g : ι → L2 κ) : ℝ :=
  ∑' k, (⟪g k, B (g k)⟫_ℂ).re

lemma trPair_nonneg {B : L2 κ →L[ℂ] L2 κ}
    (hB : ∀ x, 0 ≤ (⟪x, B x⟫_ℂ).re) (g : ι → L2 κ) :
    0 ≤ trPair B g := by
  exact tsum_nonneg (fun k => hB (g k))

/-- The total trace. -/
lemma trPair_one {g : ι → L2 κ} (_hg : GramFam g) :
    trPair (ContinuousLinearMap.id ℂ (L2 κ)) g = ∑' k, ‖g k‖ ^ 2 := by
  unfold trPair
  apply tsum_congr
  intro k
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- The trace pairing is summable for bounded `B` and ℓ²-summable families. -/
lemma trPair_summable {g : ι → L2 κ} (hg : GramFam g) (B : L2 κ →L[ℂ] L2 κ) :
    Summable (fun k => (⟪g k, B (g k)⟫_ℂ).re) := by
  apply Summable.of_abs
  apply (hg.mul_left ‖B‖).of_nonneg_of_le (fun _ => abs_nonneg _)
  intro k
  calc
    |(⟪g k, B (g k)⟫_ℂ).re| ≤ ‖⟪g k, B (g k)⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖g k‖ * ‖B (g k)‖ := norm_inner_le_norm _ _
    _ ≤ ‖g k‖ * (‖B‖ * ‖g k‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

private lemma coordinate_summable {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) :
    Summable (fun p : ι × κ => (starRingEnd ℂ) (g p.1 p.2) * B (g p.1) p.2) := by
  apply Summable.of_norm
  simp only [norm_mul, norm_conj]
  apply (summable_prod_of_nonneg (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]; norm_num
  refine ⟨fun k => lp.summable_mul hp (g k) (B (g k)), ?_⟩
  apply (hg.mul_left ‖B‖).of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => by positivity))
  intro k
  calc
    _ ≤ ‖g k‖ * ‖B (g k)‖ := lp.tsum_mul_le_mul_norm' hp _ _
    _ ≤ ‖g k‖ * (‖B‖ * ‖g k‖) := by
      gcongr
      exact B.le_opNorm _
    _ = _ := by ring

private noncomputable def basisVec (j : κ) : L2 κ := by
  classical
  exact lp.single 2 j 1

private lemma trPair_eq_basis {g : ι → L2 κ} (hg : GramFam g)
    (B : L2 κ →L[ℂ] L2 κ) :
    trPair B g = ∑' j : κ, (B (gramOp g hg (basisVec j)) j).re := by
  classical
  unfold basisVec
  have hs := coordinate_summable hg B
  have hi : Summable (fun k => ⟪g k, B (g k)⟫_ℂ) := by
    simpa only [lp.inner_eq_tsum, RCLike.inner_apply, mul_comm] using hs.prod
  rw [trPair, ← Complex.re_tsum hi]
  simp only [lp.inner_eq_tsum, RCLike.inner_apply]
  simp_rw [mul_comm (B _ _) ((starRingEnd ℂ) _)]
  rw [← Summable.tsum_comm (f := fun k j => (starRingEnd ℂ) (g k j) * B (g k) j) hs]
  have hcol (j : κ) :
      ∑' k, (starRingEnd ℂ) (g k j) * B (g k) j = B (gramOp g hg (basisVec j)) j := by
    have hm := ((hg.summable_coeff (basisVec j)).hasSum.mapL B).mapL
      (lp.evalCLM ℂ (fun _ : κ => ℂ) 2 j)
    simpa only [basisVec, gramOp_apply, lp.inner_single_right, RCLike.inner_apply,
      map_one, mul_one, one_mul, map_smul, lp.evalCLM, lp.evalₗ_apply,
      LinearMap.mkContinuous_apply, smul_eq_mul, lp.coeFn_smul, Pi.smul_apply] using hm.tsum_eq
  simp_rw [hcol]
  have hsum : Summable (fun j => B (gramOp g hg (basisVec j)) j) := by
    have hh := hs.prod_symm.prod
    change Summable (fun j => ∑' k, (starRingEnd ℂ) (g k j) * B (g k) j) at hh
    simpa only [hcol] using hh
  rw [Complex.re_tsum hsum]
  rfl

/-- Family-independence: the trace pairing only depends on the Gram operator.
(Both sides equal a double sum over any orthonormal basis; proven by Fubini
for absolutely convergent double sums, using the standard ℓ² basis.) -/
lemma trPair_congr {g : ι → L2 κ} {g' : ι' → L2 κ} [Nonempty κ]
    (hg : GramFam g) (hg' : GramFam g')
    (h : gramOp g hg = gramOp g' hg') (B : L2 κ →L[ℂ] L2 κ) :
    trPair B g = trPair B g' := by
  rw [trPair_eq_basis hg, trPair_eq_basis hg', h]

/-- `tr[ρ²] ≤ ‖ρ‖ tr[ρ]` for Gram operators. -/
lemma trPair_gramOp_le {g : ι → L2 κ} (hg : GramFam g) :
    trPair (gramOp g hg) g ≤ ‖gramOp g hg‖ * ∑' k, ‖g k‖ ^ 2 := by
  rw [trPair, ← tsum_mul_left]
  exact (trPair_summable hg _).tsum_le_tsum (fun k => inner_gramOp_le_norm hg (g k))
    (hg.mul_left _)

/-! ### Compactness and the top eigenvector -/

private lemma summable_rankOne {g : ι → L2 κ} (hg : GramFam g) :
    Summable (fun k => InnerProductSpace.rankOne ℂ (g k) (g k)) := by
  apply Summable.of_norm
  simp only [InnerProductSpace.norm_rankOne, ← sq]
  exact hg

private lemma gramOp_eq_tsum_rankOne {g : ι → L2 κ} (hg : GramFam g) :
    gramOp g hg = ∑' k, InnerProductSpace.rankOne ℂ (g k) (g k) := by
  apply ContinuousLinearMap.ext
  intro x
  exact ((summable_rankOne hg).hasSum.mapL
    (ContinuousLinearMap.apply ℂ (L2 κ) x)).tsum_eq

lemma gramOp_isCompactOperator {g : ι → L2 κ} (hg : GramFam g) :
    IsCompactOperator (gramOp g hg) := by
  classical
  rw [gramOp_eq_tsum_rankOne hg]
  apply isCompactOperator_of_tendsto (summable_rankOne hg).hasSum
  apply Filter.Eventually.of_forall
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : L2 κ →L[ℂ] L2 κ))
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk]
    apply IsCompactOperator.add _ ih
    rw [InnerProductSpace.rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ (g k))).comp_clm (innerSL ℂ (g k))

/-- A nonzero Gram operator has a top eigenvector: a unit vector with
eigenvalue equal to the operator norm. -/
theorem exists_top_eigenvector {g : ι → L2 κ} (hg : GramFam g)
    (hne : gramOp g hg ≠ 0) :
    ∃ ξ : L2 κ, ‖ξ‖ = 1 ∧
      gramOp g hg ξ = ((‖gramOp g hg‖ : ℝ) : ℂ) • ξ := by
  classical
  let T := gramOp g hg
  have : Nontrivial (L2 κ) := by
    by_contra h
    have : Subsingleton (L2 κ) := not_nontrivial_iff_subsingleton.mp h
    exact hne (Subsingleton.elim _ _)
  have hs : T.toLinearMap.IsSymmetric := gramOp_symmetric hg
  obtain ⟨μ, hμ, hn⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty T)
  rw [T.spectralRadius_eq_nnnorm hs.isSelfAdjoint] at hn
  have hn' : ‖μ‖ = ‖T‖ := congrArg (fun t : ℝ≥0 => (t : ℝ)) (ENNReal.coe_injective hn)
  have hm0 : μ ≠ 0 := by
    intro hz
    have : ‖T‖ = 0 := by simpa [hz] using hn'.symm
    exact hne (norm_eq_zero.mp this)
  have he := (gramOp_isCompactOperator hg).hasEigenvalue_iff_mem_spectrum hm0 |>.mpr hμ
  have hr : (μ.re : ℂ) = μ := (RCLike.conj_eq_iff_re.mp (hs.conj_eigenvalue_eq_self he))
  have he' : Module.End.HasEigenvalue T.toLinearMap (μ.re : ℂ) := hr ▸ he
  have hp : 0 ≤ μ.re := eigenvalue_nonneg_of_nonneg he'
    (gramOp_nonneg hg)
  have hm : μ = (‖T‖ : ℂ) := by
    rw [← hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp] at hn'
    rw [← hr, hn']
  obtain ⟨v, hv, hv0⟩ := he.exists_hasEigenvector
  have hvEq : T v = μ • v := by
    change T.toLinearMap v = μ • v
    exact Module.End.mem_genEigenspace_one.mp hv
  refine ⟨(‖v‖⁻¹ : ℂ) • v, ?_, ?_⟩
  · simp [norm_smul, Complex.norm_real, hv0]
  · change T ((‖v‖⁻¹ : ℂ) • v) = _
    rw [map_smul, hvEq, hm, smul_smul, smul_smul, mul_comm]

/-! ### The residual family of a top eigenpair -/

/-- Columns of `ρ − λ |ξ⟩⟨ξ|`: project each family vector off `ξ`. -/
noncomputable def residualFam (g : ι → L2 κ) (ξ : L2 κ) : ι → L2 κ :=
  fun k => g k - ⟪ξ, g k⟫_ℂ • ξ

lemma residualFam_gramFam {g : ι → L2 κ} (hg : GramFam g) (ξ : L2 κ) :
    GramFam (residualFam g ξ) := by
  apply (hg.mul_left ((1 + ‖ξ‖ ^ 2) ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro k
  have hb : ‖residualFam g ξ k‖ ≤ (1 + ‖ξ‖ ^ 2) * ‖g k‖ := by
    calc
      _ ≤ ‖g k‖ + ‖⟪ξ, g k⟫_ℂ • ξ‖ := norm_sub_le _ _
      _ = ‖g k‖ + ‖⟪ξ, g k⟫_ℂ‖ * ‖ξ‖ := by rw [norm_smul]
      _ ≤ ‖g k‖ + (‖ξ‖ * ‖g k‖) * ‖ξ‖ := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = _ := by ring
  calc
    _ ≤ ((1 + ‖ξ‖ ^ 2) * ‖g k‖) ^ 2 := by gcongr
    _ = _ := by ring

/-- For an eigenpair `ρ ξ = λ ξ` with `‖ξ‖ = 1` and `λ = ⟪ξ, ρ ξ⟫`:
`ρ = λ |ξ⟩⟨ξ| + gramOp (residualFam g ξ)`. -/
lemma gramOp_eq_top_add_residual {g : ι → L2 κ} (hg : GramFam g)
    {ξ : L2 κ} (hξ : ‖ξ‖ = 1) {lam : ℝ}
    (heig : gramOp g hg ξ = ((lam : ℝ) : ℂ) • ξ) (x : L2 κ) :
    gramOp g hg x =
      ((lam : ℝ) : ℂ) • (⟪ξ, x⟫_ℂ • ξ)
        + gramOp (residualFam g ξ) (residualFam_gramFam hg ξ) x := by
  let P : L2 κ →L[ℂ] L2 κ := ContinuousLinearMap.id ℂ (L2 κ) -
    InnerProductSpace.rankOne ℂ ξ ξ
  have hP (y : L2 κ) : P y = y - ⟪ξ, y⟫_ℂ • ξ := rfl
  have hinner (y z : L2 κ) : ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ := by
    simp only [hP, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_conj_symm]
    ring
  have hres : gramOp (residualFam g ξ) (residualFam_gramFam hg ξ) x =
      P (gramOp g hg (P x)) := by
    have hh := ((hg.summable_coeff (P x)).hasSum.mapL P).tsum_eq
    simp only [gramOp_apply]
    rw [← hh]
    apply tsum_congr
    intro k
    change ⟪P (g k), x⟫_ℂ • P (g k) = P (⟪g k, P x⟫_ℂ • g k)
    rw [hinner, map_smul]
  have hcross (y : L2 κ) : ⟪ξ, gramOp g hg y⟫_ℂ = (lam : ℂ) * ⟪ξ, y⟫_ℂ := by
    rw [← gramOp_symmetric hg, heig, inner_smul_left]
    simp
  have hself : ⟪ξ, ξ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hξ]
  rw [hres, hP, hP, map_sub, map_smul, heig]
  simp only [inner_sub_right, inner_smul_right, hcross, hself, mul_one]
  simp only [mul_comm (⟪ξ, x⟫_ℂ) (lam : ℂ), sub_self, zero_smul, sub_zero]
  module

/-! ### Tensor families -/

/-- The product Gram family on the product index. -/
noncomputable def tensorFam (g : ι → L2 κ) (g' : ι' → L2 κ') :
    ι × ι' → L2 (κ × κ') :=
  fun p => tpPair (g p.1) (g' p.2)

lemma tensorFam_gramFam {g : ι → L2 κ} {g' : ι' → L2 κ'}
    (hg : GramFam g) (hg' : GramFam g') : GramFam (tensorFam g g') := by
  simpa only [GramFam, tensorFam, norm_tpPair, mul_pow] using
    hg.mul_of_nonneg hg' (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

private lemma coeff_coordinate {g : ι → L2 κ} (hg : GramFam g) (x : L2 κ) (j : κ) :
    ∑' k, ⟪g k, x⟫_ℂ * g k j = gramOp g hg x j := by
  exact ((hg.summable_coeff x).hasSum.mapL (lp.evalCLM ℂ (fun _ : κ => ℂ) 2 j)).tsum_eq

private lemma coeff_coordinate_summable {g : ι → L2 κ} (hg : GramFam g)
    (x : L2 κ) (j : κ) : Summable (fun k => ⟪g k, x⟫_ℂ * g k j) := by
  exact ((hg.summable_coeff x).hasSum.mapL (lp.evalCLM ℂ (fun _ : κ => ℂ) 2 j)).summable

private lemma tensor_gram_apply {g : ι → L2 κ} {g' : ι' → L2 κ'}
    (hg : GramFam g) (hg' : GramFam g') (x : L2 κ) (y : L2 κ') :
    gramOp (tensorFam g g') (tensorFam_gramFam hg hg') (tpPair x y) =
      tpPair (gramOp g hg x) (gramOp g' hg' y) := by
  apply lp.ext
  funext p
  rw [← coeff_coordinate (tensorFam_gramFam hg hg') (tpPair x y) p]
  simp only [tensorFam, inner_tpPair, tpPair_apply]
  rw [← coeff_coordinate hg x p.1, ← coeff_coordinate hg' y p.2]
  simpa only [mul_mul_mul_comm] using
    (tsum_mul_tsum_of_summable_norm (coeff_coordinate_summable hg x p.1).norm
      (coeff_coordinate_summable hg' y p.2).norm).symm

private lemma tpPair_smul (a b : ℂ) (x : L2 κ) (y : L2 κ') :
    tpPair (a • x) (b • y) = (a * b) • tpPair x y := by
  apply lp.ext
  funext p
  simp only [tpPair_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

private lemma sum_gramFam {g : ι → L2 κ} {f : ι' → L2 κ}
    (hg : GramFam g) (hf : GramFam f) : GramFam (Sum.elim g f) := by
  exact Summable.sum _ hg hf

private lemma gramOp_sum_apply {g : ι → L2 κ} {f : ι' → L2 κ}
    (hg : GramFam g) (hf : GramFam f) (x : L2 κ) :
    gramOp (Sum.elim g f) (sum_gramFam hg hf) x = gramOp g hg x + gramOp f hf x := by
  exact (hg.summable_coeff x).tsum_sum (hf.summable_coeff x)

private lemma trPair_sum {g : ι → L2 κ} {f : ι' → L2 κ}
    (hg : GramFam g) (hf : GramFam f) (B : L2 κ →L[ℂ] L2 κ) :
    trPair B (Sum.elim g f) = trPair B g + trPair B f := by
  exact (trPair_summable hg B).tsum_sum (trPair_summable hf B)

/-- **Dominance**: for a positive bounded `B` on the doubled space and a top
eigenpair `(lam, ξ)` of `ρ = gramOp g`, `tr[B ρ⊗ρ] ≥ lam² ⟪ξ⊗ξ, B ξ⊗ξ⟫`.
(Expand both tensor factors into top + residual parts; all cross terms are
`tr[B (pos ⊗ pos)] ≥ 0` because they are again tensor Gram families.) -/
theorem trPair_tensor_ge {g : ι → L2 κ} (hg : GramFam g)
    {B : L2 (κ × κ) →L[ℂ] L2 (κ × κ)}
    (hB : ∀ x, 0 ≤ (⟪x, B x⟫_ℂ).re)
    {ξ : L2 κ} (hξ : ‖ξ‖ = 1) {lam : ℝ} (_hlam : 0 ≤ lam)
    (heig : gramOp g hg ξ = ((lam : ℝ) : ℂ) • ξ) :
    lam ^ 2 * (⟪tpPair ξ ξ, B (tpPair ξ ξ)⟫_ℂ).re ≤
      trPair B (tensorFam g g) := by
  classical
  let v := tpPair ξ ξ
  let f := tensorFam g g
  have hf : GramFam f := tensorFam_gramFam hg hg
  have hv : ‖v‖ = 1 := by simp [v, norm_tpPair, hξ]
  have he : gramOp f hf v = ((lam ^ 2 : ℝ) : ℂ) • v := by
    rw [tensor_gram_apply hg hg, heig, tpPair_smul]
    simp only [← Complex.ofReal_pow, ← pow_two, v]
  let r := residualFam f v
  have hr : GramFam r := residualFam_gramFam hf v
  let t : Unit → L2 (κ × κ) := fun _ => (lam : ℂ) • v
  have ht : GramFam t := Summable.of_finite
  have : Nonempty (κ × κ) := by
    by_contra hn
    have : IsEmpty (κ × κ) := not_nonempty_iff.mp hn
    have hz : v = 0 := by apply lp.ext; funext p; exact isEmptyElim p
    simp [hz] at hv
  have hop : gramOp (Sum.elim t r) (sum_gramFam ht hr) = gramOp f hf := by
    apply ContinuousLinearMap.ext
    intro x
    rw [gramOp_sum_apply ht hr]
    rw [gramOp_eq_top_add_residual hf hv he x]
    congr 1
    simp only [gramOp_apply, t, tsum_fintype, Fintype.sum_unique, inner_smul_left,
      Complex.conj_ofReal, smul_smul, pow_two]
    congr 1
    push_cast
    ring
  rw [← trPair_congr (sum_gramFam ht hr) hf hop B, trPair_sum ht hr B]
  have htval : trPair B t = lam ^ 2 * (⟪v, B v⟫_ℂ).re := by
    simp only [trPair, t, tsum_fintype, Fintype.sum_unique, map_smul, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    ring
  rw [htval]
  exact le_add_of_nonneg_right (trPair_nonneg hB r)

end GaussianTesting
