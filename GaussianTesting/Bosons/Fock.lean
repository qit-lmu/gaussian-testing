module

/-
The bosonic Fock space in the number basis and the block-diagonal
operators used by the concrete bosonic tests.

* `FockB m := ℓ²(Fin m → ℕ)` — Mathlib's `lp _ 2`, a complete inner-product space;
* `deg` — total particle number of a basis index; all operators of interest are
  block-diagonal for `deg`, with finite blocks;
* `blockOp` — assembling a uniformly bounded family of linear maps on the finite
  blocks into a bounded operator on `ℓ²`; quadratic forms sum over blocks.

`Bosons/Lambda.lean` defines the per-block su(2) triples to which the finite Kac
inequality applies; `Bosons/ThreeCopy.lean` proves the ℓ² moment identities. `Bosons/Main.lean`
constructs `P₀`. `ClosedLambda.lean` identifies its range with the kernel of
the graph-closed generator, which `SchrodingerFockPair.lean` transports to
the physical wavefunction model.
-/
public import GaussianTesting.GradientFlow.Abstract
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate ENNReal
open Finset

noncomputable section

/-- The m-mode bosonic Fock space in the number basis: `ℓ²` over occupation vectors. -/
abbrev FockB (m : ℕ) := lp (fun _ : (Fin m → ℕ) => ℂ) 2

/-- Total particle number of an occupation vector. -/
def degB {m : ℕ} (n : Fin m → ℕ) : ℕ := ∑ j, n j

/-- Occupation vectors of total number `n` form a finite type (compositions). -/
instance degB_fiber_fintype (m n : ℕ) : Fintype {i : Fin m → ℕ // degB i = n} := by
  classical
  have hle : ∀ (x : {i : Fin m → ℕ // degB i = n}) (j : Fin m), x.1 j ≤ n := by
    intro x j
    have h1 : x.1 j ≤ ∑ k, x.1 k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : degB x.1 = n := x.2
    exact h1.trans_eq h2
  exact Fintype.ofInjective
    (f := fun x : {i : Fin m → ℕ // degB i = n} =>
      (fun j => (⟨x.1 j, Nat.lt_succ_of_le (hle x j)⟩ : Fin (n + 1))))
    (by
      intro x y hxy
      apply Subtype.ext
      funext j
      have := congrFun hxy j
      simpa [Fin.ext_iff] using this)

section BlockOp

variable {ι : Type*} (deg : ι → ℕ) [fiberFintype : ∀ n, Fintype {i // deg i = n}]

/-- The finite block space of degree `n`. -/
abbrev BlockSp (n : ℕ) := EuclideanSpace ℂ {i // deg i = n}

/-- Restriction of an `ℓ²` vector to a block. -/
def blockProj (f : lp (fun _ : ι => ℂ) 2) (n : ℕ) : BlockSp deg n :=
  WithLp.toLp 2 fun i => f i.1

/-! Private groundwork: summability over the fiber decomposition. -/

private lemma blockProj_normSq (f : lp (fun _ : ι => ℂ) 2) (n : ℕ) :
    ‖blockProj deg f n‖ ^ 2 = ∑ i : {i // deg i = n}, ‖f i.1‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rfl

lemma lpSummableNormSq (f : lp (fun _ : ι => ℂ) 2) :
    Summable fun i : ι => ‖f i‖ ^ 2 := by
  have hf := lp.memℓp f
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have := (memℓp_gen_iff h2).mp hf
  have he : ∀ i : ι, ‖f i‖ ^ (2 : ℝ≥0∞).toReal = ‖f i‖ ^ 2 := by
    intro i
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa [he] using this

omit fiberFintype in
private lemma summable_sigma_normSq [∀ n, Fintype {i // deg i = n}] (f : lp (fun _ : ι => ℂ) 2) :
    Summable fun s : Σ n, {i // deg i = n} => ‖f s.2.1‖ ^ 2 := by
  have h := lpSummableNormSq f
  exact ((Equiv.sigmaFiberEquiv deg).summable_iff
    (f := fun i : ι => ‖f i‖ ^ 2)).mpr h

private lemma tsum_normSq_eq (f : lp (fun _ : ι => ℂ) 2) :
    ∑' i : ι, ‖f i‖ ^ 2 = ∑' n : ℕ, ‖blockProj deg f n‖ ^ 2 := by
  rw [← (Equiv.sigmaFiberEquiv deg).tsum_eq (f := fun i : ι => ‖f i‖ ^ 2)]
  have hfn : (fun c : Σ n, {i // deg i = n} => ‖f ((Equiv.sigmaFiberEquiv deg) c)‖ ^ 2)
      = fun c : Σ n, {i // deg i = n} => ‖f c.2.1‖ ^ 2 := rfl
  rw [hfn, Summable.tsum_sigma' (fun b => .of_finite)
    (summable_sigma_normSq deg f)]
  congr 1
  funext n
  rw [tsum_fintype, blockProj_normSq]

lemma lpNormSqEqTsum (f : lp (fun _ : ι => ℂ) 2) :
    ‖f‖ ^ 2 = ∑' i : ι, ‖f i‖ ^ 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have := lp.norm_rpow_eq_tsum h2 f
  have hc : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [hc] at this
  simpa [Real.rpow_natCast] using this

variable {deg}

/-- The underlying function of the block operator. -/
def blockOpFun (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (f : lp (fun _ : ι => ℂ) 2) : ∀ _ : ι, ℂ :=
  fun i => T (deg i) (blockProj deg f (deg i)) ⟨i, rfl⟩

private lemma blockOpFun_fiber_sum (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (f : lp (fun _ : ι => ℂ) 2) (n : ℕ) :
    ∑ i : {i // deg i = n}, ‖blockOpFun T f i.1‖ ^ 2
      = ‖T n (blockProj deg f n)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨iv, hi⟩ := i
  subst hi
  rfl

private lemma blockOpFun_summable (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖) (f : lp (fun _ : ι => ℂ) 2) :
    Summable fun i : ι => ‖blockOpFun T f i‖ ^ 2 := by
  rw [← (Equiv.sigmaFiberEquiv deg).summable_iff
    (f := fun i : ι => ‖blockOpFun T f i‖ ^ 2)]
  apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
  constructor
  · intro n
    exact .of_finite
  · apply Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => sq_nonneg _)
      (fun n => ?_)
      ((summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mp
        (summable_sigma_normSq deg f)).2
    rw [tsum_fintype, tsum_fintype]
    calc ∑ i : {i // deg i = n}, ‖blockOpFun T f i.1‖ ^ 2
        = ‖T n (blockProj deg f n)‖ ^ 2 := blockOpFun_fiber_sum T f n
      _ ≤ ‖blockProj deg f n‖ ^ 2 := by
          have := hT n (blockProj deg f n)
          nlinarith [norm_nonneg (T n (blockProj deg f n)),
            norm_nonneg (blockProj deg f n)]
      _ = ∑ i : {i // deg i = n}, ‖f i.1‖ ^ 2 := blockProj_normSq deg f n

private lemma blockOpFun_memℓp (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖) (f : lp (fun _ : ι => ℂ) 2) :
    Memℓp (blockOpFun T f) 2 := by
  apply memℓp_gen
  have he : ∀ i : ι, ‖blockOpFun T f i‖ ^ (2 : ℝ≥0∞).toReal
      = ‖blockOpFun T f i‖ ^ 2 := by
    intro i
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa [he] using blockOpFun_summable T hT f

variable (deg)

def blockOpL (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖) :
    lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun f := ⟨blockOpFun T f, by exact blockOpFun_memℓp T hT f⟩
  map_add' := by
    intro f g
    apply lp.ext
    funext i
    have hb : blockProj deg (f + g) (deg i)
        = blockProj deg f (deg i) + blockProj deg g (deg i) := by
      ext j
      simp [blockProj]
    simp only [lp.coeFn_add, Pi.add_apply]
    show blockOpFun T (f + g) i = blockOpFun T f i + blockOpFun T g i
    unfold blockOpFun
    rw [hb, map_add]
    rfl
  map_smul' := by
    intro c f
    apply lp.ext
    funext i
    have hb : blockProj deg (c • f) (deg i) = c • blockProj deg f (deg i) := by
      ext j
      simp [blockProj, lp.coeFn_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    show blockOpFun T (c • f) i = c • blockOpFun T f i
    unfold blockOpFun
    rw [hb, map_smul]
    rfl

/-- Assemble a uniformly bounded family of block maps into a bounded operator on `ℓ²`:
`(blockOp T f) i = (T (deg i)) (f|_(block of i))` at `i`. -/
def blockOp (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous (blockOpL deg T hT) 1 (by
    intro f
    rw [one_mul]
    have hsq : ‖(⟨blockOpFun T f, by exact blockOpFun_memℓp T hT f⟩ :
        lp (fun _ : ι => ℂ) 2)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      rw [lpNormSqEqTsum, lpNormSqEqTsum]
      have h1 : ∑' i : ι, ‖blockOpFun T f i‖ ^ 2
          = ∑' n : ℕ, ‖T n (blockProj deg f n)‖ ^ 2 := by
        have := tsum_normSq_eq deg
          (⟨blockOpFun T f, by exact blockOpFun_memℓp T hT f⟩ : lp (fun _ : ι => ℂ) 2)
        rw [this]
        congr 1
        funext n
        rw [show ‖blockProj deg (⟨blockOpFun T f, by exact blockOpFun_memℓp T hT f⟩ :
            lp (fun _ : ι => ℂ) 2) n‖ ^ 2
            = ∑ i : {i // deg i = n}, ‖blockOpFun T f i.1‖ ^ 2 from
          blockProj_normSq deg _ n, blockOpFun_fiber_sum T f n]
      rw [show (∑' i : ι, ‖(⟨blockOpFun T f, by exact blockOpFun_memℓp T hT f⟩ :
          lp (fun _ : ι => ℂ) 2) i‖ ^ 2) = ∑' i : ι, ‖blockOpFun T f i‖ ^ 2 from rfl,
        h1, tsum_normSq_eq deg f]
      have hsummL : Summable fun n : ℕ => ‖T n (blockProj deg f n)‖ ^ 2 := by
        have hs := (summable_sigma_of_nonneg
          (f := fun s : Σ n, {i // deg i = n} => ‖blockOpFun T f s.2.1‖ ^ 2)
          (fun _ => sq_nonneg _)).mp
          (((Equiv.sigmaFiberEquiv deg).summable_iff
            (f := fun i : ι => ‖blockOpFun T f i‖ ^ 2)).mpr
            (blockOpFun_summable T hT f))
        have h2 := hs.2
        convert h2 using 2 with n
        rw [tsum_fintype, blockOpFun_fiber_sum T f n]
      have hsummR : Summable fun n : ℕ => ‖blockProj deg f n‖ ^ 2 := by
        have hs := (summable_sigma_of_nonneg
          (f := fun s : Σ n, {i // deg i = n} => ‖f s.2.1‖ ^ 2)
          (fun _ => sq_nonneg _)).mp (summable_sigma_normSq deg f)
        have h2 := hs.2
        convert h2 using 2 with n
        rw [tsum_fintype, blockProj_normSq]
      apply hsummL.tsum_le_tsum _ hsummR
      intro n
      have := hT n (blockProj deg f n)
      nlinarith [norm_nonneg (T n (blockProj deg f n)),
        norm_nonneg (blockProj deg f n)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg f)
      two_ne_zero).mp hsq)

@[simp] lemma blockOp_apply (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    blockOp deg T hT f i = T (deg i) (blockProj deg f (deg i)) ⟨i, rfl⟩ := by
  with_unfolding_all rfl

/-- Norms decompose over blocks. -/
lemma norm_sq_eq_tsum_blocks (f : lp (fun _ : ι => ℂ) 2) :
    ‖f‖ ^ 2 = ∑' n, ‖blockProj deg f n‖ ^ 2 := by
  rw [lpNormSqEqTsum, tsum_normSq_eq deg]

/-! Inner products over blocks. -/

omit fiberFintype in
private lemma summable_sigma_inner [∀ n, Fintype {i // deg i = n}] (f g : lp (fun _ : ι => ℂ) 2) :
    Summable fun s : Σ n, {i // deg i = n} => ⟪f s.2.1, g s.2.1⟫_ℂ := by
  have h := ((Equiv.sigmaFiberEquiv deg).summable_iff
    (f := fun i : ι => ⟪f i, g i⟫_ℂ)).mpr (lp.summable_inner f g)
  exact h

/-- Quadratic forms of block operators sum over blocks. -/
lemma inner_blockOp (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖) (f : lp (fun _ : ι => ℂ) 2) :
    ⟪f, blockOp deg T hT f⟫_ℂ
      = ∑' n, ⟪blockProj deg f n, T n (blockProj deg f n)⟫_ℂ := by
  rw [lp.inner_eq_tsum,
    ← (Equiv.sigmaFiberEquiv deg).tsum_eq
      (f := fun i : ι => ⟪f i, blockOp deg T hT f i⟫_ℂ)]
  have hcv : (fun c : Σ n, {i // deg i = n} =>
      ⟪f ((Equiv.sigmaFiberEquiv deg) c),
        blockOp deg T hT f ((Equiv.sigmaFiberEquiv deg) c)⟫_ℂ)
      = fun c : Σ n, {i // deg i = n} =>
        ⟪f c.2.1, blockOp deg T hT f c.2.1⟫_ℂ := rfl
  rw [hcv, Summable.tsum_sigma' (fun b => .of_finite)
      (summable_sigma_inner deg f (blockOp deg T hT f))]
  congr 1
  funext n
  rw [tsum_fintype]
  rw [show ⟪blockProj deg f n, T n (blockProj deg f n)⟫_ℂ
      = ∑ i : {i // deg i = n},
          ⟪blockProj deg f n i, T n (blockProj deg f n) i⟫_ℂ from
    PiLp.inner_apply _ _]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨iv, hi⟩ := i
  subst hi
  rfl

/-- Blockwise symmetric maps give self-adjoint block operators. -/
lemma blockOp_symmetric (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖)
    (hsym : ∀ n, (T n).IsSymmetric) (f g : lp (fun _ : ι => ℂ) 2) :
    ⟪blockOp deg T hT f, g⟫_ℂ = ⟪f, blockOp deg T hT g⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    ← (Equiv.sigmaFiberEquiv deg).tsum_eq
      (f := fun i : ι => ⟪blockOp deg T hT f i, g i⟫_ℂ),
    ← (Equiv.sigmaFiberEquiv deg).tsum_eq
      (f := fun i : ι => ⟪f i, blockOp deg T hT g i⟫_ℂ)]
  have hcv1 : (fun c : Σ n, {i // deg i = n} =>
      ⟪blockOp deg T hT f ((Equiv.sigmaFiberEquiv deg) c),
        g ((Equiv.sigmaFiberEquiv deg) c)⟫_ℂ)
      = fun c : Σ n, {i // deg i = n} =>
        ⟪blockOp deg T hT f c.2.1, g c.2.1⟫_ℂ := rfl
  have hcv2 : (fun c : Σ n, {i // deg i = n} =>
      ⟪f ((Equiv.sigmaFiberEquiv deg) c),
        blockOp deg T hT g ((Equiv.sigmaFiberEquiv deg) c)⟫_ℂ)
      = fun c : Σ n, {i // deg i = n} =>
        ⟪f c.2.1, blockOp deg T hT g c.2.1⟫_ℂ := rfl
  rw [hcv1, hcv2,
    Summable.tsum_sigma' (fun b => .of_finite)
      (summable_sigma_inner deg (blockOp deg T hT f) g),
    Summable.tsum_sigma' (fun b => .of_finite)
      (summable_sigma_inner deg f (blockOp deg T hT g))]
  congr 1
  funext n
  rw [tsum_fintype, tsum_fintype]
  have hL : ∑ i : {i // deg i = n},
      ⟪blockOp deg T hT f i.1, g i.1⟫_ℂ
      = ⟪T n (blockProj deg f n), blockProj deg g n⟫_ℂ := by
    rw [show ⟪T n (blockProj deg f n), blockProj deg g n⟫_ℂ
        = ∑ i : {i // deg i = n},
            ⟪T n (blockProj deg f n) i, blockProj deg g n i⟫_ℂ from
      PiLp.inner_apply _ _]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨iv, hi⟩ := i
    subst hi
    rfl
  have hR : ∑ i : {i // deg i = n},
      ⟪f i.1, blockOp deg T hT g i.1⟫_ℂ
      = ⟪blockProj deg f n, T n (blockProj deg g n)⟫_ℂ := by
    rw [show ⟪blockProj deg f n, T n (blockProj deg g n)⟫_ℂ
        = ∑ i : {i // deg i = n},
            ⟪blockProj deg f n i, T n (blockProj deg g n) i⟫_ℂ from
      PiLp.inner_apply _ _]
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨iv, hi⟩ := i
    subst hi
    rfl
  rw [hL, hR, hsym n]

/-- Blockwise idempotents give idempotent block operators. -/
lemma blockOp_idem (T : ∀ n, BlockSp deg n →ₗ[ℂ] BlockSp deg n)
    (hT : ∀ n (v : BlockSp deg n), ‖T n v‖ ≤ ‖v‖)
    (hidem : ∀ n, T n ∘ₗ T n = T n) :
    blockOp deg T hT ∘L blockOp deg T hT = blockOp deg T hT := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  have happ : ∀ (g : lp (fun _ : ι => ℂ) 2) {n : ℕ} (j : ι) (h : deg j = n),
      blockOp deg T hT g j = T n (blockProj deg g n) ⟨j, h⟩ := by
    intro g n j h
    subst h
    rfl
  have hb : blockProj deg (blockOp deg T hT f) (deg i)
      = T (deg i) (blockProj deg f (deg i)) := by
    ext j
    show blockOp deg T hT f j.1 = T (deg i) (blockProj deg f (deg i)) j
    rw [happ f j.1 j.2]
  show blockOpFun T (blockOp deg T hT f) i = blockOpFun T f i
  unfold blockOpFun
  rw [hb, ← LinearMap.comp_apply, hidem]

end BlockOp

/-! ### The two-copy `TensorSquare` on `ℓ²`

`tp f g := ((i,j) ↦ f i * g j)` lands in `ℓ²(ι × κ)` with multiplicative norm; the
inner-product factorization is a `tsum` Fubini argument; the swap is reindexing along
`Equiv.prodComm`. -/

/-- The elementary-tensor structure on `ℓ²(ι × ι)`. -/
def lpTensorSquare (ι : Type*) :
    TensorSquare (lp (fun _ : ι => ℂ) 2) (lp (fun _ : ι × ι => ℂ) 2) := by
  classical
  let H : Type _ := lp (fun _ : ι => ℂ) 2
  let K : Type _ := lp (fun _ : ι × ι => ℂ) 2
  have hs (f g : H) : Summable (fun p : ι × ι => ‖f p.1 * g p.2‖ ^ 2) := by
    simpa only [norm_mul, mul_pow] using
      (lpSummableNormSq f).mul_of_nonneg (lpSummableNormSq g)
        (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  let t (f g : H) : K := ⟨fun p => f p.1 * g p.2, by
    apply memℓp_gen
    simpa only [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using hs f g⟩
  have ht (f g : H) : ‖t f g‖ = ‖f‖ * ‖g‖ := by
    have he : ‖t f g‖ ^ 2 = (‖f‖ * ‖g‖) ^ 2 := by
      rw [lpNormSqEqTsum]
      change (∑' p : ι × ι, ‖f p.1 * g p.2‖ ^ 2) = _
      simp_rw [norm_mul, mul_pow]
      rw [((lpSummableNormSq f).mul_of_nonneg (lpSummableNormSq g)
        (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)).tsum_prod'
          (fun i => (lpSummableNormSq g).mul_left (‖f i‖ ^ 2))]
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right, ← lpNormSqEqTsum, ← lpNormSqEqTsum]
    nlinarith [norm_nonneg (t f g), mul_nonneg (norm_nonneg f) (norm_nonneg g)]
  let tl : H →ₗ[ℂ] H →ₗ[ℂ] K :=
    { toFun := fun f =>
        { toFun := t f
          map_add' := by
            intro g h
            apply lp.ext
            funext p
            change f p.1 * (g p.2 + h p.2) = f p.1 * g p.2 + f p.1 * h p.2
            ring
          map_smul' := by
            intro c g
            apply lp.ext
            funext p
            change f p.1 * (c * g p.2) = c * (f p.1 * g p.2)
            ring }
      map_add' := by
        intro f g
        apply LinearMap.ext
        intro h
        apply lp.ext
        funext p
        change (f p.1 + g p.1) * h p.2 = f p.1 * h p.2 + g p.1 * h p.2
        ring
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro g
        apply lp.ext
        funext p
        change (c * f p.1) * g p.2 = c * (f p.1 * g p.2)
        ring }
  let tp := tl.mkContinuous₂ 1 (by
    intro f g
    change ‖t f g‖ ≤ _
    rw [ht, one_mul])
  let sw (f : K) : K := ⟨fun p => f (p.2, p.1), by
    apply memℓp_gen
    have h := (Equiv.prodComm ι ι).summable_iff.mpr (lpSummableNormSq f)
    simpa only [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, Function.comp_def, Equiv.prodComm_apply, Prod.swap] using h⟩
  have hsw (f : K) : ‖sw f‖ = ‖f‖ := by
    have he : ‖sw f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [lpNormSqEqTsum, lpNormSqEqTsum]
      exact (Equiv.prodComm ι ι).tsum_eq (fun p => ‖f p‖ ^ 2)
    nlinarith [norm_nonneg (sw f), norm_nonneg f]
  refine { tp := tp, inner_tp := ?_, swap :=
    { toLinearEquiv :=
        { toFun := sw
          invFun := sw
          left_inv := fun f => by apply lp.ext; rfl
          right_inv := fun f => by apply lp.ext; rfl
          map_add' := by
            intro f g
            apply lp.ext
            funext p
            rfl
          map_smul' := by
            intro c f
            apply lp.ext
            funext p
            rfl }
      norm_map' := hsw }, swap_tp := ?_ }
  · intro a b c d
    change ⟪t a b, t c d⟫_ℂ = _
    rw [lp.inner_eq_tsum]
    have hi (p : ι × ι) : ⟪t a b p, t c d p⟫_ℂ =
        ⟪a p.1, c p.1⟫_ℂ * ⟪b p.2, d p.2⟫_ℂ := by
      simp only [t, RCLike.inner_apply, map_mul]
      ring
    simp_rw [hi]
    have hsum : Summable (fun p : ι × ι => ⟪t a b p, t c d p⟫_ℂ) :=
      lp.summable_inner (t a b) (t c d)
    simp_rw [hi] at hsum
    rw [hsum.tsum_prod' (fun i => (lp.summable_inner (𝕜 := ℂ) b d).mul_left (⟪a i, c i⟫_ℂ))]
    simp_rw [tsum_mul_left]
    rw [tsum_mul_right, lp.inner_eq_tsum, lp.inner_eq_tsum]
  · intro a b
    apply lp.ext
    funext p
    change a p.2 * b p.1 = b p.1 * a p.2
    exact mul_comm _ _

end

end GaussianTesting
