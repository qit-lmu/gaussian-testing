module

/-
Three copies of `ℓ²` and the embedded two-copy test operators (the ℓ² analogue of the
finite-dimensional `GradientFlow/Defs.lean` + `Moments.lean` + the `p12_PF`
identification of `Fermions/SO3Bridge.lean`). Regrouping summable series gives
the inner-product decompositions and moments on `ℓ²`.

Contents:
* slice maps `ℓ²(ι³) → ℓ²(ι²)` fixing one coordinate, with the `tsum` inner-product
  decompositions `⟪F,G⟫ = Σ'_k ⟪slice_k F, slice_k G⟫`;
* the curry embeddings `q12/q13/q23` of a bounded two-copy operator into three copies,
  bounded, symmetric/idempotent-preserving, with explicit action on elementary tensors;
* `tp3lp`, the elementary triple tensor, and the moment identities for
  `Slp Q := (q12 Q + q13 Q + q23 Q)/3` in the state `ψ⊗ψ⊗ψ`:
  `⟪Ψ, Slp Ψ⟫ = p(ψ)` and `⟪Slp Ψ, Slp Ψ⟫ = (p + 2q)/3` (Lemma 3.2 on ℓ²).
-/
public import GaussianTesting.Bosons.Fock
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate ENNReal
open Finset

noncomputable section

variable {ι : Type*}

/-- `ℓ²` over an index type. -/
abbrev L2 (κ : Type*) := lp (fun _ : κ => ℂ) 2

lemma summable_normSq {κ : Type*} (F : L2 κ) :
    Summable fun i => ‖F i‖ ^ 2 := by
  have h := (memℓp_gen_iff (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num)).mp
    (lp.memℓp F)
  simpa only [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] using h

lemma mem_of_summable_normSq {κ : Type*} {f : κ → ℂ}
    (h : Summable fun i => ‖f i‖ ^ 2) : Memℓp f 2 := by
  apply memℓp_gen
  simpa only [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] using h

/-! ### Slices -/

/-- Fix the third coordinate of an `ℓ²(ι³)` vector. -/
def sl3 (F : L2 (ι × ι × ι)) (k : ι) : L2 (ι × ι) := by
  refine ⟨fun q => F (q.1, q.2, k), mem_of_summable_normSq ?_⟩
  exact (summable_normSq F).comp_injective (by
    intro a b h
    simpa only [Prod.mk.injEq, Prod.ext_iff, and_true, true_and] using h)

@[simp] lemma sl3_apply (F : L2 (ι × ι × ι)) (k : ι) (q : ι × ι) :
    sl3 F k q = F (q.1, q.2, k) := by
  rfl

/-- Fix the first coordinate. -/
def sl1 (F : L2 (ι × ι × ι)) (i : ι) : L2 (ι × ι) := by
  refine ⟨fun q => F (i, q.1, q.2), mem_of_summable_normSq ?_⟩
  exact (summable_normSq F).comp_injective (by
    intro a b h
    simpa only [Prod.mk.injEq, Prod.ext_iff, and_true, true_and] using h)

@[simp] lemma sl1_apply (F : L2 (ι × ι × ι)) (i : ι) (q : ι × ι) :
    sl1 F i q = F (i, q.1, q.2) := by
  rfl

/-- Fix the second coordinate. -/
def sl2 (F : L2 (ι × ι × ι)) (j : ι) : L2 (ι × ι) := by
  refine ⟨fun q => F (q.1, j, q.2), mem_of_summable_normSq ?_⟩
  exact (summable_normSq F).comp_injective (by
    intro a b h
    simpa only [Prod.mk.injEq, Prod.ext_iff, and_true, true_and] using h)

@[simp] lemma sl2_apply (F : L2 (ι × ι × ι)) (j : ι) (q : ι × ι) :
    sl2 F j q = F (q.1, j, q.2) := by
  rfl

/-- Inner products decompose over third-coordinate slices. -/
lemma inner_eq_tsum_sl3 (F G : L2 (ι × ι × ι)) :
    ⟪F, G⟫_ℂ = ∑' k, ⟪sl3 F k, sl3 G k⟫_ℂ := by
  let e : (ι × (ι × ι)) ≃ (ι × ι × ι) :=
    ⟨fun p => (p.2.1, p.2.2, p.1), fun p => (p.2.2, p.1, p.2.1), by intro p; rfl, by intro p; rfl⟩
  rw [lp.inner_eq_tsum, ← e.tsum_eq]
  have hs := (e.summable_iff (f := fun p => ⟪F p, G p⟫_ℂ)).mpr (lp.summable_inner F G)
  change (∑' p, ((fun p => ⟪F p, G p⟫_ℂ) ∘ e) p) = _
  rw [hs.tsum_prod]
  apply tsum_congr
  intro k
  rw [lp.inner_eq_tsum]
  rfl

lemma inner_eq_tsum_sl1 (F G : L2 (ι × ι × ι)) :
    ⟪F, G⟫_ℂ = ∑' i, ⟪sl1 F i, sl1 G i⟫_ℂ := by
  let e : (ι × (ι × ι)) ≃ (ι × ι × ι) :=
    ⟨fun p => p, fun p => p, by intro p; rfl, by intro p; rfl⟩
  rw [lp.inner_eq_tsum, ← e.tsum_eq]
  have hs := (e.summable_iff (f := fun p => ⟪F p, G p⟫_ℂ)).mpr (lp.summable_inner F G)
  change (∑' p, ((fun p => ⟪F p, G p⟫_ℂ) ∘ e) p) = _
  rw [hs.tsum_prod]
  apply tsum_congr
  intro k
  rw [lp.inner_eq_tsum]
  rfl

lemma inner_eq_tsum_sl2 (F G : L2 (ι × ι × ι)) :
    ⟪F, G⟫_ℂ = ∑' j, ⟪sl2 F j, sl2 G j⟫_ℂ := by
  let e : (ι × (ι × ι)) ≃ (ι × ι × ι) :=
    ⟨fun p => (p.2.1, p.1, p.2.2), fun p => (p.2.1, p.1, p.2.2), by intro p; rfl, by intro p; rfl⟩
  rw [lp.inner_eq_tsum, ← e.tsum_eq]
  have hs := (e.summable_iff (f := fun p => ⟪F p, G p⟫_ℂ)).mpr (lp.summable_inner F G)
  change (∑' p, ((fun p => ⟪F p, G p⟫_ℂ) ∘ e) p) = _
  rw [hs.tsum_prod]
  apply tsum_congr
  intro k
  rw [lp.inner_eq_tsum]
  rfl

private lemma norm_sq_eq_tsum {κ : Type*} (F : L2 κ) :
    ‖F‖ ^ 2 = ∑' i, ‖F i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) F
  simpa only [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] using h

def sliceE (e : (ι × (ι × ι)) ≃ (ι × ι × ι))
    (F : L2 (ι × ι × ι)) (k : ι) : L2 (ι × ι) :=
  ⟨fun q => F (e (k, q)), by
    exact mem_of_summable_normSq
      ((summable_normSq F).comp_injective (e.injective.comp (by
        intro a b h; exact (Prod.mk.inj h).2)))⟩

private lemma sliceE_norms (e : (ι × (ι × ι)) ≃ (ι × ι × ι))
    (F : L2 (ι × ι × ι)) :
    Summable (fun k => ‖sliceE e F k‖ ^ 2) ∧
      (∑' k, ‖sliceE e F k‖ ^ 2) = ‖F‖ ^ 2 := by
  have hs : Summable (fun p : ι × (ι × ι) => ‖F (e p)‖ ^ 2) :=
    (e.summable_iff (f := fun p => ‖F p‖ ^ 2)).mpr (summable_normSq F)
  have ht : (fun k => ‖sliceE e F k‖ ^ 2) =
      (fun k => ∑' q : ι × ι, ‖F (e (k, q))‖ ^ 2) := by
    funext k
    exact norm_sq_eq_tsum _
  rw [ht]
  refine ⟨(summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp hs |>.2, ?_⟩
  calc
    (∑' k, ∑' q, ‖F (e (k, q))‖ ^ 2) = ∑' p, ‖F (e p)‖ ^ 2 := hs.tsum_prod.symm
    _ = ∑' p, ‖F p‖ ^ 2 := e.tsum_eq (fun p => ‖F p‖ ^ 2)
    _ = ‖F‖ ^ 2 := (norm_sq_eq_tsum F).symm

private lemma sliceOp_mem (e : (ι × (ι × ι)) ≃ (ι × ι × ι))
    (Q : L2 (ι × ι) →L[ℂ] L2 (ι × ι)) (hQ : ‖Q‖ ≤ 1)
    (F : L2 (ι × ι × ι)) :
    Memℓp (fun p => Q (sliceE e F (e.symm p).1) (e.symm p).2) 2 := by
  apply mem_of_summable_normSq
  apply (e.summable_iff (f := fun p =>
    ‖Q (sliceE e F (e.symm p).1) (e.symm p).2‖ ^ 2)).mp
  change Summable (fun p : ι × (ι × ι) =>
    ‖Q (sliceE e F (e.symm (e p)).1) (e.symm (e p)).2‖ ^ 2)
  simp only [Equiv.symm_apply_apply]
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun k => summable_normSq (Q (sliceE e F k)), ?_⟩
  have ht : (fun k => ∑' q, ‖Q (sliceE e F k) q‖ ^ 2) =
      (fun k => ‖Q (sliceE e F k)‖ ^ 2) := by
    funext k; exact (norm_sq_eq_tsum _).symm
  rw [ht]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (sliceE_norms e F).1
  intro k
  have h := (Q.le_opNorm (sliceE e F k)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hQ)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

def sliceOpL (e : (ι × (ι × ι)) ≃ (ι × ι × ι))
    (Q : L2 (ι × ι) →L[ℂ] L2 (ι × ι)) (hQ : ‖Q‖ ≤ 1) :
    L2 (ι × ι × ι) →ₗ[ℂ] L2 (ι × ι × ι) where
  toFun F := ⟨fun p => Q (sliceE e F (e.symm p).1) (e.symm p).2,
    by exact sliceOp_mem e Q hQ F⟩
  map_add' F G := by
    have h : ∀ k, sliceE e (F + G) k = sliceE e F k + sliceE e G k := by
      intro k; apply lp.ext; funext q; simp [sliceE]; rfl
    apply lp.ext; funext p
    simp [h]; rfl
  map_smul' c F := by
    have h : ∀ k, sliceE e (c • F) k = c • sliceE e F k := by
      intro k; apply lp.ext; funext q; simp [sliceE, lp.coeFn_smul]
    apply lp.ext; funext p
    simp [h, lp.coeFn_smul]

def sliceOp (e : (ι × (ι × ι)) ≃ (ι × ι × ι))
    (Q : L2 (ι × ι) →L[ℂ] L2 (ι × ι)) (hQ : ‖Q‖ ≤ 1) :
    L2 (ι × ι × ι) →L[ℂ] L2 (ι × ι × ι) :=
  (sliceOpL e Q hQ).mkContinuous 1 (by
    intro F
    rw [one_mul]
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : 2 ≠ 0)).mp
    rw [norm_sq_eq_tsum]
    change (∑' p, ‖Q (sliceE e F (e.symm p).1) (e.symm p).2‖ ^ 2) ≤ _
    rw [← e.tsum_eq (fun p => ‖Q (sliceE e F (e.symm p).1) (e.symm p).2‖ ^ 2)]
    change (∑' p : ι × (ι × ι),
      ‖Q (sliceE e F (e.symm (e p)).1) (e.symm (e p)).2‖ ^ 2) ≤ _
    simp only [Equiv.symm_apply_apply]
    have hs : Summable (fun p : ι × (ι × ι) => ‖Q (sliceE e F p.1) p.2‖ ^ 2) := by
      have h := summable_normSq (sliceOpL e Q hQ F)
      have h' := (e.summable_iff (f := fun p => ‖(sliceOpL e Q hQ F) p‖ ^ 2)).mpr h
      change Summable (fun p : ι × (ι × ι) =>
        ‖Q (sliceE e F (e.symm (e p)).1) (e.symm (e p)).2‖ ^ 2) at h'
      simpa only [Equiv.symm_apply_apply] using h' 
    rw [hs.tsum_prod]
    have ht : (fun k => ∑' q, ‖Q (sliceE e F k) q‖ ^ 2) =
        (fun k => ‖Q (sliceE e F k)‖ ^ 2) := by
      funext k; exact (norm_sq_eq_tsum _).symm
    rw [ht]
    rw [← (sliceE_norms e F).2]
    apply Summable.tsum_le_tsum
    · intro k
      have h := (Q.le_opNorm (sliceE e F k)).trans
        (mul_le_of_le_one_left (norm_nonneg _) hQ)
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    · have h := (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp hs |>.2
      rw [ht] at h
      exact h
    · exact (sliceE_norms e F).1)

private lemma sliceOp_apply (e : (ι × (ι × ι)) ≃ (ι × ι × ι))
    (Q : L2 (ι × ι) →L[ℂ] L2 (ι × ι)) (hQ : ‖Q‖ ≤ 1)
    (F : L2 (ι × ι × ι)) (p : ι × ι × ι) :
    sliceOp e Q hQ F p = Q (sliceE e F (e.symm p).1) (e.symm p).2 := by
  have h : sliceOp e Q hQ F = sliceOpL e Q hQ F :=
    LinearMap.mkContinuous_apply _ _ _ _
  rw [h]
  with_unfolding_all rfl

/-! ### Curry embeddings of a bounded two-copy operator -/

variable (Q : L2 (ι × ι) →L[ℂ] L2 (ι × ι))

/-- `Q ⊗ I`: apply `Q` to the 1,2-slices. -/
def q12 (hQ : ‖Q‖ ≤ 1) : L2 (ι × ι × ι) →L[ℂ] L2 (ι × ι × ι) := by
  exact sliceOp
    ⟨fun p => (p.2.1, p.2.2, p.1), fun p => (p.2.2, p.1, p.2.1), by intro p; rfl, by intro p; rfl⟩ Q hQ

/-- `I ⊗ Q` on the 2,3-slices. -/
def q23 (hQ : ‖Q‖ ≤ 1) : L2 (ι × ι × ι) →L[ℂ] L2 (ι × ι × ι) := by
  exact sliceOp
    ⟨fun p => p, fun p => p, by intro p; rfl, by intro p; rfl⟩ Q hQ

/-- `Q` on the 1,3-slices. -/
def q13 (hQ : ‖Q‖ ≤ 1) : L2 (ι × ι × ι) →L[ℂ] L2 (ι × ι × ι) := by
  exact sliceOp
    ⟨fun p => (p.2.1, p.1, p.2.2), fun p => (p.2.1, p.1, p.2.2), by intro p; rfl, by intro p; rfl⟩ Q hQ

lemma sl3_q12 (hQ : ‖Q‖ ≤ 1) (F : L2 (ι × ι × ι)) (k : ι) :
    sl3 (q12 Q hQ F) k = Q (sl3 F k) := by
  apply lp.ext
  funext q
  rw [sl3_apply]
  simp only [q12, sliceOp_apply]
  rfl

lemma sl1_q23 (hQ : ‖Q‖ ≤ 1) (F : L2 (ι × ι × ι)) (i : ι) :
    sl1 (q23 Q hQ F) i = Q (sl1 F i) := by
  apply lp.ext
  funext q
  rw [sl1_apply]
  simp only [q23, sliceOp_apply]
  rfl

lemma sl2_q13 (hQ : ‖Q‖ ≤ 1) (F : L2 (ι × ι × ι)) (j : ι) :
    sl2 (q13 Q hQ F) j = Q (sl2 F j) := by
  apply lp.ext
  funext q
  rw [sl2_apply]
  simp only [q13, sliceOp_apply]
  rfl

/-! ### Elementary tensors -/

/-- The elementary triple tensor on `ℓ²`. -/
def tp3lp (ψ φ χ : L2 ι) : L2 (ι × ι × ι) := by
  refine ⟨fun p => ψ p.1 * φ p.2.1 * χ p.2.2, mem_of_summable_normSq ?_⟩
  have hφχ := (summable_normSq φ).mul_of_nonneg (summable_normSq χ)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have h := (summable_normSq ψ).mul_of_nonneg hφχ
    (fun _ => sq_nonneg _) (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  simpa only [norm_mul, mul_pow, mul_assoc] using h

@[simp] lemma tp3lp_apply (ψ φ χ : L2 ι) (p : ι × ι × ι) :
    tp3lp ψ φ χ p = ψ p.1 * φ p.2.1 * χ p.2.2 := by
  rfl

private lemma lpTensorSquare_tp_apply (f g : L2 ι) (i j : ι) :
    (lpTensorSquare ι).tp f g (i,j) = f i * g j := by
  with_unfolding_all rfl

private lemma lpTensorSquare_swap_apply (f : L2 (ι × ι)) (i j : ι) :
    (lpTensorSquare ι).swap f (i,j) = f (j,i) := by
  with_unfolding_all rfl

/-- Slices of elementary triple tensors. -/
lemma sl3_tp3lp (ψ φ χ : L2 ι) (k : ι) :
    sl3 (tp3lp ψ φ χ) k = χ k • (lpTensorSquare ι).tp ψ φ := by
  apply lp.ext
  funext q
  rcases q with ⟨a, b⟩
  simp only [sl3_apply, tp3lp_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lpTensorSquare_tp_apply]
  ring

lemma sl1_tp3lp (ψ φ χ : L2 ι) (i : ι) :
    sl1 (tp3lp ψ φ χ) i = ψ i • (lpTensorSquare ι).tp φ χ := by
  apply lp.ext
  funext q
  rcases q with ⟨a, b⟩
  simp only [sl1_apply, tp3lp_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lpTensorSquare_tp_apply]
  ring

lemma sl2_tp3lp (ψ φ χ : L2 ι) (j : ι) :
    sl2 (tp3lp ψ φ χ) j = φ j • (lpTensorSquare ι).tp ψ χ := by
  apply lp.ext
  funext q
  rcases q with ⟨a, b⟩
  simp only [sl2_apply, tp3lp_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lpTensorSquare_tp_apply]
  ring

/-! ### The moment identities (Lemma 3.2 on ℓ²)

With `T := lpTensorSquare ι`, `P` an acceptance projection with `‖P‖ ≤ 1`, and
`Ψ := tp3lp ψ ψ ψ` for a unit `ψ`, the averaged embedded operator

    `Slp P hP := (1/3)(q12 P + q13 P + q23 P)`

satisfies `⟪Ψ, Slp Ψ⟫ = p(ψ)` and `⟪Slp Ψ, Slp Ψ⟫ = (p(ψ) + 2 q(ψ))/3`, by the same
first-moment/cross-term computations as the finite `Moments.lean` (with the matrix
symmetry of `P ψ⊗ψ` from swap-invariance, and the `Kvec` coordinate formula from the
Riesz definition of the abstract contraction). -/

variable {P : L2 (ι × ι) →L[ℂ] L2 (ι × ι)}

/-- The averaged three-copy operator. -/
def Slp (hP : ‖P‖ ≤ 1) : L2 (ι × ι × ι) →L[ℂ] L2 (ι × ι × ι) :=
  (3 : ℂ)⁻¹ • (q12 P hP + q13 P hP + q23 P hP)

/-- Each sliced operator is a contraction, so their average has norm at most one. -/
theorem Slp_norm_le_one (hP : ‖P‖ ≤ 1) : ‖Slp hP‖ ≤ 1 := by
  have hs (e : (ι × (ι × ι)) ≃ (ι × ι × ι)) : ‖sliceOp e P hP‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have h12 : ‖q12 P hP‖ ≤ 1 := hs _
  have h13 : ‖q13 P hP‖ ≤ 1 := hs _
  have h23 : ‖q23 P hP‖ ≤ 1 := hs _
  rw [Slp, norm_smul, norm_inv]
  norm_num only [Complex.norm_ofNat]
  linarith [norm_add_le (q12 P hP) (q13 P hP),
    norm_add_le (q12 P hP + q13 P hP) (q23 P hP)]

/-- A slice-wise copy of an orthogonal projection has a nonnegative quadratic form. -/
private lemma sliced_projection_isPositive (hacc : (lpTensorSquare ι).IsAcceptance P)
    (Q : L2 (ι × ι × ι) →L[ℂ] L2 (ι × ι × ι))
    (slice : L2 (ι × ι × ι) → ι → L2 (ι × ι))
    (decompose : ∀ F G, ⟪F, G⟫_ℂ = ∑' j, ⟪slice F j, slice G j⟫_ℂ)
    (act : ∀ F j, slice (Q F) j = P (slice F j)) : Q.IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex Q).mpr
  intro F
  have h : ⟪Q F, F⟫_ℂ = ⟪Q F, Q F⟫_ℂ := by
    rw [decompose (Q F) F, decompose (Q F) (Q F)]
    apply tsum_congr
    intro j
    rw [act, ← hacc.symmetric, show P (P (slice F j)) = P (slice F j) from
      DFunLike.congr_fun hacc.idem _]
  rw [h]
  exact ⟨inner_self_ofReal_re _, inner_self_nonneg⟩

open scoped ComplexOrder in
/-- The average of the three embeddings of an acceptance projection is positive. -/
theorem Slp_nonneg (hP : ‖P‖ ≤ 1) (hacc : (lpTensorSquare ι).IsAcceptance P) :
    0 ≤ Slp hP := by
  have h12 := sliced_projection_isPositive hacc _ sl3 inner_eq_tsum_sl3 (sl3_q12 P hP)
  have h13 := sliced_projection_isPositive hacc _ sl2 inner_eq_tsum_sl2 (sl2_q13 P hP)
  have h23 := sliced_projection_isPositive hacc _ sl1 inner_eq_tsum_sl1 (sl1_q23 P hP)
  have hc : 0 ≤ (3 : ℂ)⁻¹ := by simp
  exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (((h12.add h13).add h23).smul_of_nonneg hc)

private def row (M : L2 (ι × ι)) (i : ι) : L2 ι :=
  ⟨fun j => M (i,j), mem_of_summable_normSq
    ((summable_normSq M).comp_injective (by intro a b h; exact (Prod.mk.inj h).2))⟩

private lemma inner_row (ψ : L2 ι) (M : L2 (ι × ι)) (i : ι) :
    ⟪ψ, row M i⟫_ℂ = (lpTensorSquare ι).contr ψ M i := by
  classical
  have h := (lpTensorSquare ι).inner_contr ψ M (lp.single 2 i 1)
  rw [lp.inner_single_left] at h
  simp only [RCLike.inner_apply, map_one, mul_one] at h
  rw [h, lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hs := lp.summable_inner (𝕜 := ℂ)
    ((lpTensorSquare ι).tp (lp.single 2 i 1) ψ) M
  rw [hs.tsum_prod]
  simp only [lpTensorSquare_tp_apply, lp.coeFn_single, Pi.single_apply,
    RCLike.inner_apply, map_mul]
  simp only [apply_ite, map_one, map_zero]
  symm
  rw [tsum_eq_single i]
  · simp [row]
  · intro b hb
    simp [hb]

/-- Coordinates of the abstract Riesz contraction on `ℓ²`:
`(K_ψψ)(i) = Σ'_j conj (ψ j) · (P ψ⊗ψ)(i, j)`. -/
lemma KvecA_apply_lp (ψ : L2 ι) (i : ι) :
    (lpTensorSquare ι).KvecA P ψ i
      = ∑' j, conj (ψ j) * (P ((lpTensorSquare ι).tp ψ ψ)) (i, j) := by
  unfold TensorSquare.KvecA
  rw [← inner_row, lp.inner_eq_tsum]
  simp [row, RCLike.inner_apply, mul_comm]

private lemma tsum_inner_smul (ψ : L2 ι) (A B : L2 (ι × ι)) :
    (∑' i, ⟪ψ i • A, ψ i • B⟫_ℂ) = ⟪ψ, ψ⟫_ℂ * ⟪A, B⟫_ℂ := by
  simp only [inner_smul_left, inner_smul_right]
  simp_rw [← mul_assoc]
  rw [tsum_mul_right]
  simp only [lp.inner_eq_tsum, RCLike.inner_apply]

private lemma first12 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) :
    ⟪tp3lp ψ ψ ψ, q12 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ * ⟪(lpTensorSquare ι).tp ψ ψ, P ((lpTensorSquare ι).tp ψ ψ)⟫_ℂ := by
  rw [inner_eq_tsum_sl3]
  simp_rw [sl3_q12, sl3_tp3lp, map_smul]
  exact tsum_inner_smul _ _ _

private lemma first13 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) :
    ⟪tp3lp ψ ψ ψ, q13 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ * ⟪(lpTensorSquare ι).tp ψ ψ, P ((lpTensorSquare ι).tp ψ ψ)⟫_ℂ := by
  rw [inner_eq_tsum_sl2]
  simp_rw [sl2_q13, sl2_tp3lp, map_smul]
  exact tsum_inner_smul _ _ _

private lemma first23 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) :
    ⟪tp3lp ψ ψ ψ, q23 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ * ⟪(lpTensorSquare ι).tp ψ ψ, P ((lpTensorSquare ι).tp ψ ψ)⟫_ℂ := by
  rw [inner_eq_tsum_sl1]
  simp_rw [sl1_q23, sl1_tp3lp, map_smul]
  exact tsum_inner_smul _ _ _

/-- First moment. -/
theorem inner_tp3lp_Slp (hP : ‖P‖ ≤ 1)
    (hacc : (lpTensorSquare ι).IsAcceptance P) {ψ : L2 ι} (hψ : ‖ψ‖ = 1) :
    ⟪tp3lp ψ ψ ψ, Slp hP (tp3lp ψ ψ ψ)⟫_ℂ
      = (((lpTensorSquare ι).accProbA P ψ : ℝ) : ℂ) := by
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  simp only [Slp, smul_apply, add_apply,
    inner_smul_right, inner_add_right, first12, first13, first23,
    (lpTensorSquare ι).inner_tp_P_self hacc, hn, one_mul]
  ring

private lemma act12 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) (i j k : ι) :
    q12 P hP (tp3lp ψ ψ ψ) (i,j,k) =
      ψ k * P ((lpTensorSquare ι).tp ψ ψ) (i,j) := by
  have h := congrArg (fun f : L2 (ι × ι) => f (i,j))
    (sl3_q12 P hP (tp3lp ψ ψ ψ) k)
  simpa [sl3_tp3lp, lp.coeFn_smul] using h

private lemma act13 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) (i j k : ι) :
    q13 P hP (tp3lp ψ ψ ψ) (i,j,k) =
      ψ j * P ((lpTensorSquare ι).tp ψ ψ) (i,k) := by
  have h := congrArg (fun f : L2 (ι × ι) => f (i,k))
    (sl2_q13 P hP (tp3lp ψ ψ ψ) j)
  simpa [sl2_tp3lp, lp.coeFn_smul] using h

private lemma act23 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) (i j k : ι) :
    q23 P hP (tp3lp ψ ψ ψ) (i,j,k) =
      ψ i * P ((lpTensorSquare ι).tp ψ ψ) (j,k) := by
  have h := congrArg (fun f : L2 (ι × ι) => f (j,k))
    (sl1_q23 P hP (tp3lp ψ ψ ψ) i)
  simpa [sl1_tp3lp, lp.coeFn_smul] using h

private lemma matrix_symm (hacc : (lpTensorSquare ι).IsAcceptance P)
    (ψ : L2 ι) (i j : ι) :
    P ((lpTensorSquare ι).tp ψ ψ) (i,j) = P ((lpTensorSquare ι).tp ψ ψ) (j,i) := by
  have h := hacc.swap_comm ((lpTensorSquare ι).tp ψ ψ)
  rw [TensorSquare.swap_tp] at h
  exact congrArg (fun f : L2 (ι × ι) => f (i,j)) h

private lemma cross_rows (ψ : L2 ι) (M : L2 (ι × ι)) :
    (∑' i, ⟪(lpTensorSquare ι).tp (row M i) ψ,
      (lpTensorSquare ι).tp ψ (row M i)⟫_ℂ) =
      ⟪(lpTensorSquare ι).contr ψ M, (lpTensorSquare ι).contr ψ M⟫_ℂ := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [TensorSquare.inner_tp, ← inner_conj_symm (row M i) ψ, inner_row]
  simp only [RCLike.inner_apply]
  ring

private lemma cross1213 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) :
    ⟪q12 P hP (tp3lp ψ ψ ψ), q13 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ((lpTensorSquare ι).qProbA P ψ : ℂ) := by
  rw [inner_eq_tsum_sl1]
  have h1 (i : ι) : sl1 (q12 P hP (tp3lp ψ ψ ψ)) i =
      (lpTensorSquare ι).tp (row (P ((lpTensorSquare ι).tp ψ ψ)) i) ψ := by
    apply lp.ext; funext ⟨j,k⟩
    simp [act12, lpTensorSquare_tp_apply, row, mul_comm]
  have h2 (i : ι) : sl1 (q13 P hP (tp3lp ψ ψ ψ)) i =
      (lpTensorSquare ι).tp ψ (row (P ((lpTensorSquare ι).tp ψ ψ)) i) := by
    apply lp.ext; funext ⟨j,k⟩
    simp [act13, lpTensorSquare_tp_apply, row]
  simp_rw [h1, h2]
  rw [cross_rows]
  simp [TensorSquare.qProbA, TensorSquare.KvecA, inner_self_eq_norm_sq_to_K]

private lemma cross1223 (hP : ‖P‖ ≤ 1)
    (hacc : (lpTensorSquare ι).IsAcceptance P) (ψ : L2 ι) :
    ⟪q12 P hP (tp3lp ψ ψ ψ), q23 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ((lpTensorSquare ι).qProbA P ψ : ℂ) := by
  rw [inner_eq_tsum_sl2]
  have h1 (j : ι) : sl2 (q12 P hP (tp3lp ψ ψ ψ)) j =
      (lpTensorSquare ι).tp (row (P ((lpTensorSquare ι).tp ψ ψ)) j) ψ := by
    apply lp.ext; funext ⟨i,k⟩
    simp [act12, lpTensorSquare_tp_apply, row, matrix_symm hacc ψ i j, mul_comm]
  have h2 (j : ι) : sl2 (q23 P hP (tp3lp ψ ψ ψ)) j =
      (lpTensorSquare ι).tp ψ (row (P ((lpTensorSquare ι).tp ψ ψ)) j) := by
    apply lp.ext; funext ⟨i,k⟩
    simp [act23, lpTensorSquare_tp_apply, row]
  simp_rw [h1, h2]
  rw [cross_rows]
  simp [TensorSquare.qProbA, TensorSquare.KvecA, inner_self_eq_norm_sq_to_K]

private lemma cross1323 (hP : ‖P‖ ≤ 1)
    (hacc : (lpTensorSquare ι).IsAcceptance P) (ψ : L2 ι) :
    ⟪q13 P hP (tp3lp ψ ψ ψ), q23 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ((lpTensorSquare ι).qProbA P ψ : ℂ) := by
  rw [inner_eq_tsum_sl3]
  have h1 (k : ι) : sl3 (q13 P hP (tp3lp ψ ψ ψ)) k =
      (lpTensorSquare ι).tp (row (P ((lpTensorSquare ι).tp ψ ψ)) k) ψ := by
    apply lp.ext; funext ⟨i,j⟩
    simp [act13, lpTensorSquare_tp_apply, row, matrix_symm hacc ψ i k, mul_comm]
  have h2 (k : ι) : sl3 (q23 P hP (tp3lp ψ ψ ψ)) k =
      (lpTensorSquare ι).tp ψ (row (P ((lpTensorSquare ι).tp ψ ψ)) k) := by
    apply lp.ext; funext ⟨i,j⟩
    simp [act23, lpTensorSquare_tp_apply, row, matrix_symm hacc ψ j k]
  simp_rw [h1, h2]
  rw [cross_rows]
  simp [TensorSquare.qProbA, TensorSquare.KvecA, inner_self_eq_norm_sq_to_K]

private lemma diag12 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) :
    ⟪q12 P hP (tp3lp ψ ψ ψ), q12 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ * ⟪P ((lpTensorSquare ι).tp ψ ψ), P ((lpTensorSquare ι).tp ψ ψ)⟫_ℂ := by
  rw [inner_eq_tsum_sl3]
  simp_rw [sl3_q12, sl3_tp3lp, map_smul]
  exact tsum_inner_smul _ _ _

private lemma diag13 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) :
    ⟪q13 P hP (tp3lp ψ ψ ψ), q13 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ * ⟪P ((lpTensorSquare ι).tp ψ ψ), P ((lpTensorSquare ι).tp ψ ψ)⟫_ℂ := by
  rw [inner_eq_tsum_sl2]
  simp_rw [sl2_q13, sl2_tp3lp, map_smul]
  exact tsum_inner_smul _ _ _

private lemma diag23 (hP : ‖P‖ ≤ 1) (ψ : L2 ι) :
    ⟪q23 P hP (tp3lp ψ ψ ψ), q23 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ⟪ψ, ψ⟫_ℂ * ⟪P ((lpTensorSquare ι).tp ψ ψ), P ((lpTensorSquare ι).tp ψ ψ)⟫_ℂ := by
  rw [inner_eq_tsum_sl1]
  simp_rw [sl1_q23, sl1_tp3lp, map_smul]
  exact tsum_inner_smul _ _ _

/-- Second moment. -/
theorem inner_Slp_Slp (hP : ‖P‖ ≤ 1)
    (hacc : (lpTensorSquare ι).IsAcceptance P) {ψ : L2 ι} (hψ : ‖ψ‖ = 1) :
    ⟪Slp hP (tp3lp ψ ψ ψ), Slp hP (tp3lp ψ ψ ψ)⟫_ℂ
      = ((((lpTensorSquare ι).accProbA P ψ
          + 2 * (lpTensorSquare ι).qProbA P ψ) / 3 : ℝ) : ℂ) := by
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have hd : ⟪P ((lpTensorSquare ι).tp ψ ψ), P ((lpTensorSquare ι).tp ψ ψ)⟫_ℂ =
      ((lpTensorSquare ι).accProbA P ψ : ℂ) := by
    rw [hacc.symmetric, show P (P ((lpTensorSquare ι).tp ψ ψ)) =
      P ((lpTensorSquare ι).tp ψ ψ) from DFunLike.congr_fun hacc.idem _]
    exact (lpTensorSquare ι).inner_tp_P_self hacc ψ
  have hc1 := cross1213 hP ψ
  have hc2 := cross1223 hP hacc ψ
  have hc3 := cross1323 hP hacc ψ
  have hr1 : ⟪q13 P hP (tp3lp ψ ψ ψ), q12 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ((lpTensorSquare ι).qProbA P ψ : ℂ) := by
    rw [← inner_conj_symm, hc1, Complex.conj_ofReal]
  have hr2 : ⟪q23 P hP (tp3lp ψ ψ ψ), q12 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ((lpTensorSquare ι).qProbA P ψ : ℂ) := by
    rw [← inner_conj_symm, hc2, Complex.conj_ofReal]
  have hr3 : ⟪q23 P hP (tp3lp ψ ψ ψ), q13 P hP (tp3lp ψ ψ ψ)⟫_ℂ =
      ((lpTensorSquare ι).qProbA P ψ : ℂ) := by
    rw [← inner_conj_symm, hc3, Complex.conj_ofReal]
  simp only [Slp, smul_apply, add_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, diag12, diag13, diag23, hn, one_mul, hd,
    hc1, hc2, hc3, hr1, hr2, hr3]
  push_cast
  simp only [map_inv₀, map_ofNat]
  ring

/-- Lemma 3.3 on ℓ²: a quadratic-form gap for `Slp` yields the Łojasiewicz data. -/
theorem lojasiewiczData_of_Slp_gap (hP : ‖P‖ ≤ 1)
    (hacc : (lpTensorSquare ι).IsAcceptance P) {α : ℝ}
    (hgap : ∀ F : L2 (ι × ι × ι),
      0 ≤ (⟪F, Slp hP (Slp hP F)⟫_ℂ
            - (1 + α) * ⟪F, Slp hP F⟫_ℂ + α * ⟪F, F⟫_ℂ).re) :
    (lpTensorSquare ι).LojasiewiczData P α := by
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp (Slp_nonneg hP hacc)).inner_left_eq_inner_right
  intro ψ hψ
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have ht : ⟪tp3lp ψ ψ ψ, tp3lp ψ ψ ψ⟫_ℂ = 1 := by
    rw [inner_eq_tsum_sl3]
    simp_rw [sl3_tp3lp]
    rw [tsum_inner_smul, TensorSquare.inner_tp, hn]
    norm_num
  have hg := hgap (tp3lp ψ ψ ψ)
  rw [← hs, inner_Slp_Slp hP hacc hψ, inner_tp3lp_Slp hP hacc hψ, ht] at hg
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, mul_zero, sub_zero] at hg
  nlinarith


end

end GaussianTesting
