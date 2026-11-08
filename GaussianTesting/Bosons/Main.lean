module

/-
The bosonic mean-zero kernel projection and its blockwise estimates.

The two-copy projection `P0B` is assembled from the finite particle-number
kernels of `lambdaB`. `KernelCore.lean` and `ClosedLambda.lean` identify it
with the kernel projection of the graph-closed generator, and
`SchrodingerFockPair.lean` transports it to the physical wavefunction model.

This file also retains coordinate moment, gradient, and certainty-witness
estimates. The manuscript's Theorem 6.4 is proved in
`PhysicalMeanZeroRobustness.lean`, using the physical SO(3) copy action,
Theorem 4.1, and the projective-flow proof of Theorem 3.4.
-/
public import GaussianTesting.Bosons.Lambda
public import GaussianTesting.Bosons.ThreeCopy

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace
open Finset

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {m : ℕ}

/-- Two-copy total particle number. -/
def degB2 {m : ℕ} (p : (Fin m → ℕ) × (Fin m → ℕ)) : ℕ := degB p.1 + degB p.2

instance degB2_fiber_fintype (m n : ℕ) :
    Fintype {p : (Fin m → ℕ) × (Fin m → ℕ) // degB2 p = n} := by
  classical
  have hle (x : {p : (Fin m → ℕ) × (Fin m → ℕ) // degB2 p = n}) :
      degB x.1.1 ≤ n ∧ degB x.1.2 ≤ n := by
    have := x.2
    dsimp [degB2] at this
    omega
  have hb (v : Fin m → ℕ) (j : Fin m) : v j ≤ degB v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact Fintype.ofInjective
    (f := fun x : {p : (Fin m → ℕ) × (Fin m → ℕ) // degB2 p = n} =>
      ((fun j => (⟨x.1.1 j, Nat.lt_succ_of_le ((hb _ j).trans (hle x).1)⟩ : Fin (n+1))),
       (fun j => (⟨x.1.2 j, Nat.lt_succ_of_le ((hb _ j).trans (hle x).2)⟩ : Fin (n+1)))))
    (by
      intro x y h
      apply Subtype.ext
      apply Prod.ext
      · funext j
        exact congrArg Fin.val (congrFun (congrArg Prod.fst h) j)
      · funext j
        exact congrArg Fin.val (congrFun (congrArg Prod.snd h) j))

/-- The two-copy algebraic `Λ = i Σ_l (a_l ⊗ a†_l − a†_l ⊗ a_l)` (on finitely
supported coefficients), via the first two copy-embeddings specialized to pairs. -/
def lambdaB (m : ℕ) : (((Fin m → ℕ) × (Fin m → ℕ)) →₀ ℂ) →ₗ[ℂ]
    (((Fin m → ℕ) × (Fin m → ℕ)) →₀ ℂ) :=
  Complex.I • ∑ l : Fin m,
    ((Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
        (Finsupp.lmapDomain ℂ ℂ (fun i => (i, p.2)) ((aF l) (Finsupp.single p.1 1))))
      ∘ₗ (Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
        (Finsupp.lmapDomain ℂ ℂ (fun j => (p.1, j)) ((adF l) (Finsupp.single p.2 1))))
    - (Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
        (Finsupp.lmapDomain ℂ ℂ (fun i => (i, p.2)) ((adF l) (Finsupp.single p.1 1))))
      ∘ₗ (Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
        (Finsupp.lmapDomain ℂ ℂ (fun j => (p.1, j)) ((aF l) (Finsupp.single p.2 1)))))

abbrev FA2 (m : ℕ) := ((Fin m → ℕ) × (Fin m → ℕ)) →₀ ℂ

def copyL (A : FA m →ₗ[ℂ] FA m) : FA2 m →ₗ[ℂ] FA2 m :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (Finsupp.lmapDomain ℂ ℂ (fun i => (i, p.2)) (A (Finsupp.single p.1 1)))

def copyR (A : FA m →ₗ[ℂ] FA m) : FA2 m →ₗ[ℂ] FA2 m :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (Finsupp.lmapDomain ℂ ℂ (fun j => (p.1, j)) (A (Finsupp.single p.2 1)))

def ConservesDeg2 (T : FA2 m →ₗ[ℂ] FA2 m) : Prop :=
  ∀ p q, q ∈ (T (Finsupp.single p 1)).support → degB2 q = degB2 p

private lemma degB_update (p : Fin m → ℕ) (l : Fin m) (a : ℕ) :
    degB (Function.update p l a) + p l = degB p + a := by
  classical
  have h (v : Fin m → ℕ) : degB v = (∑ j ∈ univ.erase l, v j) + v l :=
    (sum_erase_add _ _ (mem_univ l)).symm
  rw [h, h, Function.update_self]
  have he : (∑ j ∈ univ.erase l, Function.update p l a j) =
      ∑ j ∈ univ.erase l, p j := by
    apply sum_congr rfl
    intro j hj
    exact Function.update_of_ne (ne_of_mem_erase hj) _ _
  rw [he]
  omega

private lemma conserves_smul {T : FA2 m →ₗ[ℂ] FA2 m}
    (hT : ConservesDeg2 T) (c : ℂ) : ConservesDeg2 (c • T) := by
  intro p q h
  exact hT p q (Finsupp.support_smul h)

private lemma conserves_sub {S T : FA2 m →ₗ[ℂ] FA2 m}
    (hS : ConservesDeg2 S) (hT : ConservesDeg2 T) : ConservesDeg2 (S - T) := by
  intro p q h
  rcases Finset.mem_union.mp (Finsupp.support_sub h) with h | h
  · exact hS p q h
  · exact hT p q h

private lemma conserves_sum {ι : Type*} (s : Finset ι) (T : ι → FA2 m →ₗ[ℂ] FA2 m)
    (hT : ∀ i ∈ s, ConservesDeg2 (T i)) : ConservesDeg2 (∑ i ∈ s, T i) := by
  classical
  intro p q h
  by_contra hq
  have hz : (∑ i ∈ s, T i) (Finsupp.single p 1) q = 0 := by
    simp only [LinearMap.sum_apply, Finsupp.finsetSum_apply]
    apply sum_eq_zero
    intro i hi
    by_contra hn
    exact hq (hT i hi p q (Finsupp.mem_support_iff.mpr hn))
  exact Finsupp.mem_support_iff.mp h hz

private lemma conserve12f (l : Fin m) :
    ConservesDeg2 (copyL (aF l) ∘ₗ copyR (adF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copyL, copyR, aF, adF,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.lmapDomain_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.1 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have h1 := degB_update p.1 l (p.1 l - 1)
  have h2 := degB_update p.2 l (p.2 l + 1)
  dsimp [degB2]
  omega

private lemma conserve12r (l : Fin m) :
    ConservesDeg2 (copyL (adF l) ∘ₗ copyR (aF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copyL, copyR, aF, adF,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.lmapDomain_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.2 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have h1 := degB_update p.1 l (p.1 l + 1)
  have h2 := degB_update p.2 l (p.2 l - 1)
  dsimp [degB2]
  omega

/-- `Λ` conserves the two-copy degree. -/
lemma conservesDeg2_lambdaB (m : ℕ) :
    ∀ p q, q ∈ (lambdaB m (Finsupp.single p 1)).support → degB2 q = degB2 p := by
  change ConservesDeg2 (Complex.I • ∑ l : Fin m,
    (copyL (aF l) ∘ₗ copyR (adF l) - copyL (adF l) ∘ₗ copyR (aF l)))
  apply conserves_smul
  apply conserves_sum
  intro l _
  exact conserves_sub (conserve12f l) (conserve12r l)

def blockLift2 (n : ℕ) : BlockSp (degB2 (m := m)) n →ₗ[ℂ] FA2 m where
  toFun v := ∑ p, v p • Finsupp.single p.1 1
  map_add' v w := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PiLp.smul_apply, smul_smul, smul_eq_mul, Finset.smul_sum, RingHom.id_apply]

lemma blockLift2_apply (n : ℕ) (v : BlockSp (degB2 (m := m)) n)
    (q : (Fin m → ℕ) × (Fin m → ℕ)) :
    blockLift2 n v q = if h : degB2 q = n then v ⟨q, h⟩ else 0 := by
  classical
  simp only [blockLift2, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : degB2 q = n
  · rw [dite_eq_left h, Finset.sum_eq_single (⟨q, h⟩ : {q // degB2 q = n})]
    · simp
    · intro p _ hp
      exact ite_eq_right (fun he => hp (Subtype.ext he))
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro p _
    exact ite_eq_right (fun (hp : p.1 = q) => h (hp ▸ p.2))

/-- Restriction of a degree-conserving algebraic endomorphism to the finite block of
degree `n`, as a linear map on `BlockSp degB2 n`. -/
def toBlock2 (T : FA2 m →ₗ[ℂ] FA2 m) (n : ℕ) :
    BlockSp (degB2 (m := m)) n →ₗ[ℂ] BlockSp (degB2 (m := m)) n := by
  exact
    { toFun := fun v => WithLp.toLp 2 fun q => T (blockLift2 n v) q.1
      map_add' := by
        intro v w
        ext q
        simp [map_add]
      map_smul' := by
        intro c v
        ext q
        simp [map_smul] }

lemma blockLift2_toBlock2 {T : FA2 m →ₗ[ℂ] FA2 m}
    (hT : ConservesDeg2 T) (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    blockLift2 n (toBlock2 T n v) = T (blockLift2 n v) := by
  classical
  ext q
  rw [blockLift2_apply]
  split_ifs with hq
  · rfl
  · symm
    change (T (∑ p : {p // degB2 p = n}, v p • Finsupp.single p.1 1)) q = 0
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply]
    apply Finset.sum_eq_zero
    intro p _
    have hz : (T (Finsupp.single p.1 1)) q = 0 := by
      by_contra h
      exact hq ((hT p.1 q (Finsupp.mem_support_iff.mpr h)).trans p.2)
    rw [hz, smul_zero]

/-- Restriction respects composition for degree-conserving maps. -/
lemma toBlock2_comp {S T : FA2 m →ₗ[ℂ] FA2 m} (_hS : ConservesDeg2 S)
    (hT : ConservesDeg2 T) (n : ℕ) :
    toBlock2 (S ∘ₗ T) n = toBlock2 S n ∘ₗ toBlock2 T n := by
  apply LinearMap.ext
  intro v
  ext q
  change (S (T (blockLift2 n v))) q.1 =
    (S (blockLift2 n (toBlock2 T n v))) q.1
  rw [blockLift2_toBlock2 hT]


lemma toBlock2_apply (T : FA2 m →ₗ[ℂ] FA2 m) (n : ℕ)
    (v : BlockSp (degB2 (m := m)) n) (q : {q // degB2 q = n}) :
    toBlock2 T n v q = ∑ p : {p // degB2 p = n}, v p * (T (Finsupp.single p.1 1)) q.1 := by
  classical
  change (T (∑ p : {p // degB2 p = n}, v p • Finsupp.single p.1 1)) q.1 = _
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

lemma toBlock2_symmetric (T : FA2 m →ₗ[ℂ] FA2 m)
    (h : ∀ p q, (T (Finsupp.single p 1)) q = star ((T (Finsupp.single q 1)) p))
    (n : ℕ) : (toBlock2 T n).IsSymmetric := by
  classical
  intro v w
  simp only [PiLp.inner_apply, RCLike.inner_apply, toBlock2_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [h]
  simp
  all_goals ring

/-- The per-block `Λ` matrices. -/
def lambdaBlock (m n : ℕ) :
    BlockSp (degB2 (m := m)) n →ₗ[ℂ] BlockSp (degB2 (m := m)) n :=
  toBlock2 (lambdaB m) n

lemma aF_entry (l : Fin m) (p q : Fin m → ℕ) :
    (aF l (Finsupp.single p 1)) q =
      star ((adF l (Finsupp.single q 1)) p) := by
  classical
  by_cases hp : p l = 0
  · have hn : Function.update q l (q l + 1) ≠ p := by
      intro h
      have hh := congrFun h l
      simp only [Function.update_self] at hh
      omega
    simp [aF, adF, Finsupp.lsum_single, hp, hn]
  · have hpos : 0 < p l := Nat.pos_of_ne_zero hp
    by_cases h : Function.update p l (p l - 1) = q
    · subst q
      have hh : (↑(p l - 1) : ℝ) + 1 = (p l : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hpos
      simp [aF, adF, Finsupp.lsum_single, Function.update_self, Function.update_idem,
        Nat.sub_add_cancel hpos, Function.update_eq_self, hh]
    · have hn : Function.update q l (q l + 1) ≠ p := by
        intro he
        apply h
        rw [← he, Function.update_self, Nat.add_sub_cancel, Function.update_idem,
          Function.update_eq_self]
      simp [aF, adF, Finsupp.lsum_single, h, hn]

lemma adF_entry (l : Fin m) (p q : Fin m → ℕ) :
    (adF l (Finsupp.single p 1)) q = star ((aF l (Finsupp.single q 1)) p) := by
  simpa only [star_star] using congrArg star (aF_entry l q p).symm

private lemma pair_entry12f (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copyL (aF l) ∘ₗ copyR (adF l)) (Finsupp.single p 1)) q =
      ((aF l (Finsupp.single p.1 1)) q.1) * ((adF l (Finsupp.single p.2 1)) q.2) := by
  classical
  rcases p with ⟨p1,p2⟩
  rcases q with ⟨q1,q2⟩
  simp [copyL, copyR, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  all_goals ring

private lemma pair_entry12r (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copyL (adF l) ∘ₗ copyR (aF l)) (Finsupp.single p 1)) q =
      ((adF l (Finsupp.single p.1 1)) q.1) * ((aF l (Finsupp.single p.2 1)) q.2) := by
  classical
  rcases p with ⟨p1,p2⟩
  rcases q with ⟨q1,q2⟩
  simp [copyL, copyR, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  all_goals ring

private lemma pair_adj12 (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copyL (aF l) ∘ₗ copyR (adF l)) (Finsupp.single p 1)) q =
      star (((copyL (adF l) ∘ₗ copyR (aF l)) (Finsupp.single q 1)) p) := by
  rw [pair_entry12f, pair_entry12r]
  rw [aF_entry l p.1 q.1, adF_entry l p.2 q.2]
  simp only [star_mul]
  ring

private lemma lambdaB_entry (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (lambdaB m (Finsupp.single p 1)) q = star ((lambdaB m (Finsupp.single q 1)) p) := by
  classical
  change ( (Complex.I • ∑ l : Fin m,
    (copyL (aF l) ∘ₗ copyR (adF l) - copyL (adF l) ∘ₗ copyR (aF l)))
      (Finsupp.single p 1)) q = star (((Complex.I • ∑ l : Fin m,
    (copyL (aF l) ∘ₗ copyR (adF l) - copyL (adF l) ∘ₗ copyR (aF l)))
      (Finsupp.single q 1)) p)
  simp only [ LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.sub_apply, smul_eq_mul,
    star_mul, star_sum, Complex.star_def, Complex.conj_I, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hf := pair_adj12 l p q
  have hr := congrArg star (pair_adj12 l q p)
  simp only [star_star] at hr
  rw [hf, ← hr]
  simp only [Complex.star_def, map_sub]
  ring

lemma lambdaBlock_isSymmetric (m n : ℕ) : (lambdaBlock m n).IsSymmetric := by
  exact toBlock2_symmetric (lambdaB m) lambdaB_entry n

/-- The bosonic acceptance projection: block-diagonal assembly of the finite kernel
projections of `Λ`. -/
def P0B (m : ℕ) : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 →L[ℂ]
    lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 :=
  blockOp (degB2 (m := m))
    (fun n => ((LinearMap.ker (lambdaBlock m n)).starProjection :
        BlockSp (degB2 (m := m)) n →L[ℂ] BlockSp (degB2 (m := m)) n))
    (by intro n v; exact (LinearMap.ker (lambdaBlock m n)).norm_starProjection_apply_le v)

def swapFiber (m n : ℕ) :
    {p // degB2 (m := m) p = n} ≃ {p // degB2 (m := m) p = n} where
  toFun p := ⟨(p.1.2, p.1.1), by simpa [degB2, Nat.add_comm] using p.2⟩
  invFun p := ⟨(p.1.2, p.1.1), by simpa [degB2, Nat.add_comm] using p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def swapBlock (m n : ℕ) : BlockSp (degB2 (m := m)) n →ₗ[ℂ]
    BlockSp (degB2 (m := m)) n where
  toFun v := WithLp.toLp 2 (fun p => v (swapFiber m n p))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma swapBlock_sq (v : BlockSp (degB2 (m := m)) n) :
    swapBlock m n (swapBlock m n v) = v := rfl

lemma swapBlock_inner (v w : BlockSp (degB2 (m := m)) n) :
    ⟪swapBlock m n v, swapBlock m n w⟫_ℂ = ⟪v,w⟫_ℂ := by
  simp only [PiLp.inner_apply]
  exact Equiv.sum_comp (swapFiber m n) (fun p => ⟪v p, w p⟫_ℂ)

private lemma lambdaB_swap_entry (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (lambdaB m (Finsupp.single (p.2,p.1) 1)) q =
      -(lambdaB m (Finsupp.single p 1)) (q.2,q.1) := by
  classical
  change ((Complex.I • ∑ l : Fin m,
    (copyL (aF l) ∘ₗ copyR (adF l) - copyL (adF l) ∘ₗ copyR (aF l)))
      (Finsupp.single (p.2,p.1) 1)) q =
    -((Complex.I • ∑ l : Fin m,
    (copyL (aF l) ∘ₗ copyR (adF l) - copyL (adF l) ∘ₗ copyR (aF l)))
      (Finsupp.single p 1)) (q.2,q.1)
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.sub_apply, smul_eq_mul,
    pair_entry12f, pair_entry12r, ← Finset.sum_neg_distrib, ← mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

private lemma lambdaBlock_swap (v : BlockSp (degB2 (m := m)) n) :
    lambdaBlock m n (swapBlock m n v) = -swapBlock m n (lambdaBlock m n v) := by
  classical
  ext q
  simp only [lambdaBlock, PiLp.neg_apply]
  change toBlock2 (lambdaB m) n (swapBlock m n v) q =
    -(toBlock2 (lambdaB m) n v) (swapFiber m n q)
  simp only [toBlock2_apply]
  change (∑ p, v (swapFiber m n p) * (lambdaB m (Finsupp.single p.1 1)) q.1) =
    -(∑ p, v p * (lambdaB m (Finsupp.single p.1 1)) (q.1.2,q.1.1))
  rw [← Equiv.sum_comp (swapFiber m n)
    (fun p => v (swapFiber m n p) * (lambdaB m (Finsupp.single p.1 1)) q.1)]
  simp only [swapFiber, Equiv.coe_fn_mk, lambdaB_swap_entry, mul_neg,
    Finset.sum_neg_distrib]

private lemma projection_swap (v : BlockSp (degB2 (m := m)) n) :
    (LinearMap.ker (lambdaBlock m n)).starProjection (swapBlock m n v) =
      swapBlock m n ((LinearMap.ker (lambdaBlock m n)).starProjection v) := by
  let K := LinearMap.ker (lambdaBlock m n)
  have preserve {w : BlockSp (degB2 (m := m)) n} (hw : w ∈ K) :
      swapBlock m n w ∈ K := by
    change lambdaBlock m n (swapBlock m n w) = 0
    rw [lambdaBlock_swap, LinearMap.mem_ker.mp hw, map_zero, neg_zero]
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
    (preserve (K.starProjection_apply_mem v))
  intro w hw
  have hz := K.starProjection_inner_eq_zero v (swapBlock m n w) (preserve hw)
  have hi := swapBlock_inner (v - K.starProjection v) (swapBlock m n w)
  rw [swapBlock_sq, map_sub] at hi
  exact hi.trans hz

lemma blockProj_swap (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
    (n : ℕ) :
    blockProj degB2 ((lpTensorSquare (Fin m → ℕ)).swap f) n =
      swapBlock m n (blockProj degB2 f n) := by
  rfl

/-- `P₀` is an acceptance projection for the elementary-tensor structure on ℓ². -/
theorem P0B_isAcceptance (m : ℕ) :
    (lpTensorSquare ((Fin m → ℕ))).IsAcceptance (P0B m) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact blockOp_symmetric _ _ _ (fun n =>
      (LinearMap.ker (lambdaBlock m n)).starProjection_isSymmetric)
  · apply blockOp_idem
    intro n
    apply LinearMap.ext
    intro v
    exact (LinearMap.ker (lambdaBlock m n)).starProjection_eq_self_iff.mpr
      ((LinearMap.ker (lambdaBlock m n)).starProjection_apply_mem v)
  · intro f
    apply lp.ext
    funext p
    change P0B m ((lpTensorSquare (Fin m → ℕ)).swap f) p = P0B m f (p.2,p.1)
    have happ (g : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
        (q : (Fin m → ℕ) × (Fin m → ℕ)) {n : ℕ} (hq : degB2 q = n) :
        P0B m g q = (LinearMap.ker (lambdaBlock m n)).starProjection
          (blockProj degB2 g n) ⟨q,hq⟩ := by subst n; rfl
    rw [happ _ p rfl, blockProj_swap, projection_swap,
      happ f (p.2,p.1) (n := degB2 p) (by simp [degB2, Nat.add_comm])]
    rfl

theorem P0B_norm_le_one (m : ℕ) : ‖P0B m‖ ≤ 1 := by
  unfold P0B blockOp
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) _

private lemma K12_lambdaB_entry
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (K12 m (Finsupp.single p 1)) q =
      (lambdaB m (Finsupp.single (p.1,p.2.1) 1)) (q.1,q.2.1) *
        (Finsupp.single p.2.2 (1 : ℂ)) q.2.2 := by
  classical
  simp only [K12, lambdaB, LinearMap.smul_apply, LinearMap.sum_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul, mul_assoc,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, copy2, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

def thirdSliceIndex (n : ℕ) (k : Fin m → ℕ) (hk : degB k ≤ n)
    (q : {p // degB2 (m := m) p = n - degB k}) : {p // degB3 (m := m) p = n} :=
  ⟨(q.1.1,q.1.2,k), by have := q.2; dsimp [degB3, degB2] at *; omega⟩

def thirdSliceBlock (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) : BlockSp (degB2 (m := m)) (n - degB k) :=
  WithLp.toLp 2 (fun q => v (thirdSliceIndex n k hk q))

private lemma K12_thirdSlice (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    thirdSliceBlock n (toBlock3 (K12 m) n v) k hk =
      lambdaBlock m (n - degB k) (thirdSliceBlock n v k hk) := by
  classical
  ext q
  have hm (T : FA3 m →ₗ[ℂ] FA3 m) (r : {p // degB3 p = n}) :
      toBlock3 T n v r = ∑ p : {p // degB3 p = n},
        v p * (T (Finsupp.single p.1 1)) r.1 := by
    change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) r.1 = _
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  change toBlock3 (K12 m) n v (thirdSliceIndex n k hk q) = _
  rw [hm, lambdaBlock, toBlock2_apply]
  simp_rw [K12_lambdaB_entry]
  symm
  apply Fintype.sum_of_injective (thirdSliceIndex n k hk)
  · intro a b h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p => p.1.1) h) (congrArg (fun p => p.1.2.1) h)
  · intro p hp
    have hne : p.1.2.2 ≠ k := by
      intro he
      apply hp
      have hd : degB2 (p.1.1,p.1.2.1) = n - degB k := by
        have := p.2
        dsimp [degB3] at this
        rw [he] at this
        dsimp [degB2]
        omega
      refine ⟨⟨(p.1.1,p.1.2.1),hd⟩, ?_⟩
      apply Subtype.ext
      dsimp [thirdSliceIndex]
      exact Prod.ext rfl (Prod.ext rfl he.symm)
    simp [thirdSliceIndex, hne]
  · intro p
    simp [thirdSliceIndex, thirdSliceBlock]

private lemma ker_K12_thirdSlices (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    v ∈ LinearMap.ker (toBlock3 (K12 m) n) ↔
      ∀ (k : Fin m → ℕ) (hk : degB k ≤ n),
        thirdSliceBlock n v k hk ∈ LinearMap.ker (lambdaBlock m (n - degB k)) := by
  constructor
  · intro hv k hk
    apply LinearMap.mem_ker.mpr
    rw [← K12_thirdSlice, LinearMap.mem_ker.mp hv]
    rfl
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext q
    have hq := q.2
    dsimp [degB3] at hq
    have hk : degB q.1.2.2 ≤ n := by omega
    have hd : degB2 (q.1.1,q.1.2.1) = n - degB q.1.2.2 := by
      dsimp [degB2]
      omega
    have he := congrArg (fun w : BlockSp (degB2 (m := m)) (n - degB q.1.2.2) =>
      w ⟨(q.1.1,q.1.2.1),hd⟩) (K12_thirdSlice n v q.1.2.2 hk)
    rw [LinearMap.mem_ker.mp (hv q.1.2.2 hk)] at he
    exact he

lemma summable_inner_blocks {ι : Type*} (d : ι → ℕ)
    [∀ n, Fintype {i // d i = n}] (f g : L2 ι) :
    Summable (fun n => ⟪blockProj d f n, blockProj d g n⟫_ℂ) := by
  have hs : Summable (fun p : Σ n, {i // d i = n} => ⟪f p.2.1,g p.2.1⟫_ℂ) :=
    (Equiv.sigmaFiberEquiv d).summable_iff.mpr (lp.summable_inner f g)
  have ht := hs.sigma' (fun _ => Summable.of_finite)
  simpa only [tsum_fintype, PiLp.inner_apply, blockProj] using ht

lemma inner_blocks {ι : Type*} (d : ι → ℕ)
    [∀ n, Fintype {i // d i = n}] (f g : L2 ι) :
    ⟪f,g⟫_ℂ = ∑' n, ⟪blockProj d f n, blockProj d g n⟫_ℂ := by
  have hs : Summable (fun p : Σ n, {i // d i = n} => ⟪f p.2.1,g p.2.1⟫_ℂ) :=
    (Equiv.sigmaFiberEquiv d).summable_iff.mpr (lp.summable_inner f g)
  rw [lp.inner_eq_tsum, ← (Equiv.sigmaFiberEquiv d).tsum_eq
    (f := fun i => ⟪f i,g i⟫_ℂ)]
  change (∑' p : Σ n, {i // d i = n}, ⟪f p.2.1,g p.2.1⟫_ℂ) = _
  rw [Summable.tsum_sigma' (fun _ => .of_finite) hs]
  congr 1
  funext n
  rw [tsum_fintype, PiLp.inner_apply]
  rfl

private lemma gap_of_blocks (S : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) →L[ℂ]
    L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)))
    (hS : ∀ F n, blockProj degB3 (S F) n =
      kacT (blockTriple m n) (blockProj degB3 F n))
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
    0 ≤ (⟪F, S (S F)⟫_ℂ - (1 + (7 / 12 : ℝ)) * ⟪F, S F⟫_ℂ +
      (7 / 12 : ℝ) * ⟪F,F⟫_ℂ).re := by
  let a : ℂ := ((7 / 12 : ℝ) : ℂ)
  let G := S (S F) - (1 + a) • S F + a • F
  have he : ⟪F,G⟫_ℂ = ⟪F,S (S F)⟫_ℂ - (1+a) * ⟪F,S F⟫_ℂ + a * ⟪F,F⟫_ℂ := by
    simp [G, inner_add_right, inner_sub_right, inner_smul_right]
  change 0 ≤ (⟪F,S (S F)⟫_ℂ - (1+a) * ⟪F,S F⟫_ℂ + a * ⟪F,F⟫_ℂ).re
  rw [← he, inner_blocks degB3 F G,
    Complex.re_tsum (summable_inner_blocks degB3 F G)]
  apply tsum_nonneg
  intro n
  have hb : blockProj degB3 G n =
      ((kacT (blockTriple m n) - LinearMap.id) ∘ₗ
        (kacT (blockTriple m n) - a • LinearMap.id)) (blockProj degB3 F n) := by
    have hadd (x y : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
        blockProj degB3 (x+y) n = blockProj degB3 x n + blockProj degB3 y n := rfl
    have hsub (x y : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
        blockProj degB3 (x-y) n = blockProj degB3 x n - blockProj degB3 y n := rfl
    have hsm (c : ℂ) (x : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
        blockProj degB3 (c • x) n = c • blockProj degB3 x n := rfl
    dsimp [G]
    rw [hadd, hsub, hsm, hsm, hS, hS]
    simp only [map_sub, map_smul, add_smul, one_smul]
    abel
  rw [hb]
  exact kacT_gap (blockTriple m n) (blockProj degB3 F n)

/-! ### The per-generator projection identification (third-coordinate case) -/

instance degLe_fintype (m n : ℕ) : Fintype {k : Fin m → ℕ // degB k ≤ n} := by
  classical
  have hb (v : Fin m → ℕ) (j : Fin m) : v j ≤ degB v :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact Fintype.ofInjective
    (f := fun x : {k : Fin m → ℕ // degB k ≤ n} =>
      (fun j => (⟨x.1 j, Nat.lt_succ_of_le ((hb _ j).trans x.2)⟩ : Fin (n + 1))))
    (by
      intro x y h
      apply Subtype.ext
      funext j
      exact congrArg Fin.val (congrFun h j))

/-- The 3-copy fiber of degree `n` fibers over the third coordinate. -/
def thirdEquiv (m n : ℕ) :
    {p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ) // degB3 p = n} ≃
      Σ k : {k : Fin m → ℕ // degB k ≤ n},
        {p : (Fin m → ℕ) × (Fin m → ℕ) // degB2 p = n - degB k.1} where
  toFun q := ⟨⟨q.1.2.2, by have := q.2; dsimp [degB3] at this; omega⟩,
    ⟨(q.1.1, q.1.2.1), by have := q.2; dsimp [degB3, degB2] at *; omega⟩⟩
  invFun s := thirdSliceIndex n s.1.1 s.1.2 s.2
  left_inv q := by
    apply Subtype.ext
    dsimp [thirdSliceIndex]
  right_inv s := by
    rcases s with ⟨k, q⟩
    dsimp [thirdSliceIndex]

/-- Block inner products decompose over third-coordinate slices. -/
lemma inner_third (n : ℕ) (x y : BlockSp (degB3 (m := m)) n) :
    ⟪x, y⟫_ℂ = ∑ k : {k : Fin m → ℕ // degB k ≤ n},
      ⟪thirdSliceBlock n x k.1 k.2, thirdSliceBlock n y k.1 k.2⟫_ℂ := by
  classical
  rw [show ⟪x, y⟫_ℂ = ∑ q, ⟪x q, y q⟫_ℂ from PiLp.inner_apply _ _]
  rw [← Fintype.sum_equiv (thirdEquiv m n).symm
    (fun s => ⟪x ((thirdEquiv m n).symm s), y ((thirdEquiv m n).symm s)⟫_ℂ)
    (fun q => ⟪x q, y q⟫_ℂ) (fun s => rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ⟪thirdSliceBlock n x k.1 k.2, thirdSliceBlock n y k.1 k.2⟫_ℂ
      = ∑ q, ⟪thirdSliceBlock n x k.1 k.2 q, thirdSliceBlock n y k.1 k.2 q⟫_ℂ from
    PiLp.inner_apply _ _]
  rfl

/-- Slices are linear in the block vector. -/
lemma thirdSliceBlock_sub (n : ℕ) (x y : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    thirdSliceBlock n (x - y) k hk
      = thirdSliceBlock n x k hk - thirdSliceBlock n y k hk := rfl

/-- The dependent application formula for `P0B`. -/
private lemma P0B_apply' (m : ℕ) (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
    {n : ℕ} (i : (Fin m → ℕ) × (Fin m → ℕ)) (h : degB2 i = n) :
    P0B m f i = ((LinearMap.ker (lambdaBlock m n)).starProjection :
        BlockSp (degB2 (m := m)) n →L[ℂ] BlockSp (degB2 (m := m)) n)
      (blockProj degB2 f n) ⟨i, h⟩ := by
  subst h
  exact blockOp_apply _ _ _ f i

/-- The slice formula: slices of `q12 (P0B) F` are the projected slices of `F`. -/
private lemma q12_P0B_slice (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    thirdSliceBlock n (blockProj degB3 (q12 (P0B m) (P0B_norm_le_one m) F) n) k hk
      = ((LinearMap.ker (lambdaBlock m (n - degB k))).starProjection :
          BlockSp (degB2 (m := m)) (n - degB k) →L[ℂ]
            BlockSp (degB2 (m := m)) (n - degB k))
        (thirdSliceBlock n (blockProj degB3 F n) k hk) := by
  classical
  ext q
  have h1 : thirdSliceBlock n
      (blockProj degB3 (q12 (P0B m) (P0B_norm_le_one m) F) n) k hk q
      = q12 (P0B m) (P0B_norm_le_one m) F (q.1.1, q.1.2, k) := rfl
  have h2 : q12 (P0B m) (P0B_norm_le_one m) F (q.1.1, q.1.2, k)
      = P0B m (sl3 F k) (q.1.1, q.1.2) := by
    have := congrArg (fun v : L2 ((Fin m → ℕ) × (Fin m → ℕ)) => v (q.1.1, q.1.2))
      (sl3_q12 (P0B m) (P0B_norm_le_one m) F k)
    simpa using this
  have hd : degB2 (m := m) (q.1.1, q.1.2) = n - degB k := q.2
  rw [h1, h2, P0B_apply' m (sl3 F k) (q.1.1, q.1.2) hd]
  have h3 : blockProj degB2 (sl3 F k) (n - degB k)
      = thirdSliceBlock n (blockProj degB3 F n) k hk := by
    ext r
    rfl
  rw [h3]

/-- The q12-generator identification on blocks. -/
private lemma q12_block (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB3 (q12 (P0B m) (P0B_norm_le_one m) F) n
      = (LinearMap.ker (toBlock3 (K12 m) n)).starProjection
          (blockProj degB3 F n) := by
  classical
  set v := blockProj degB3 F n
  set w := blockProj degB3 (q12 (P0B m) (P0B_norm_le_one m) F) n with hw
  symm
  apply (LinearMap.ker (toBlock3 (K12 m) n)).eq_starProjection_of_mem_of_inner_eq_zero
  · -- membership: every slice of w is a projection output, hence in the slice kernel
    rw [ker_K12_thirdSlices]
    intro k hk
    rw [hw, q12_P0B_slice m F n k hk]
    exact Submodule.starProjection_apply_mem _ _
  · -- orthogonality: slicewise
    intro u hu
    rw [inner_third]
    apply Finset.sum_eq_zero
    intro k _
    rw [thirdSliceBlock_sub, hw, q12_P0B_slice m F n k.1 k.2]
    exact (LinearMap.ker (lambdaBlock m (n - degB k.1))).starProjection_inner_eq_zero
      (thirdSliceBlock n v k.1 k.2) _ ((ker_K12_thirdSlices n u).mp hu k.1 k.2)

private lemma K23_lambdaB_entry
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (K23 m (Finsupp.single p 1)) q =
      (lambdaB m (Finsupp.single (p.2.1,p.2.2) 1)) (q.2.1,q.2.2) *
        (Finsupp.single p.1 (1 : ℂ)) q.1 := by
  classical
  simp only [K23, lambdaB, LinearMap.smul_apply, LinearMap.sum_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul, mul_assoc,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy2, copy3, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private def firstSliceIndex (n : ℕ) (k : Fin m → ℕ) (hk : degB k ≤ n)
    (q : {p // degB2 (m := m) p = n - degB k}) : {p // degB3 (m := m) p = n} :=
  ⟨(k,q.1.1,q.1.2), by have := q.2; dsimp [degB3, degB2] at *; omega⟩

private def firstSliceBlock (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) : BlockSp (degB2 (m := m)) (n - degB k) :=
  WithLp.toLp 2 (fun q => v (firstSliceIndex n k hk q))

private lemma K23_firstSlice (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    firstSliceBlock n (toBlock3 (K23 m) n v) k hk =
      lambdaBlock m (n - degB k) (firstSliceBlock n v k hk) := by
  classical
  ext q
  have hm (T : FA3 m →ₗ[ℂ] FA3 m) (r : {p // degB3 p = n}) :
      toBlock3 T n v r = ∑ p : {p // degB3 p = n},
        v p * (T (Finsupp.single p.1 1)) r.1 := by
    change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) r.1 = _
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  change toBlock3 (K23 m) n v (firstSliceIndex n k hk q) = _
  rw [hm, lambdaBlock, toBlock2_apply]
  simp_rw [K23_lambdaB_entry]
  symm
  apply Fintype.sum_of_injective (firstSliceIndex n k hk)
  · intro a b h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p => p.1.2.1) h) (congrArg (fun p => p.1.2.2) h)
  · intro p hp
    have hne : p.1.1 ≠ k := by
      intro he
      apply hp
      have hd : degB2 (p.1.2.1,p.1.2.2) = n - degB k := by
        have := p.2
        dsimp [degB3] at this
        rw [he] at this
        dsimp [degB2]
        omega
      refine ⟨⟨(p.1.2.1,p.1.2.2),hd⟩, ?_⟩
      apply Subtype.ext
      dsimp [firstSliceIndex]
      exact Prod.ext he.symm (Prod.ext rfl rfl)
    simp [firstSliceIndex, hne]
  · intro p
    simp [firstSliceIndex, firstSliceBlock]

private lemma ker_K23_firstSlices (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    v ∈ LinearMap.ker (toBlock3 (K23 m) n) ↔
      ∀ (k : Fin m → ℕ) (hk : degB k ≤ n),
        firstSliceBlock n v k hk ∈ LinearMap.ker (lambdaBlock m (n - degB k)) := by
  constructor
  · intro hv k hk
    apply LinearMap.mem_ker.mpr
    rw [← K23_firstSlice, LinearMap.mem_ker.mp hv]
    rfl
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext q
    have hq := q.2
    dsimp [degB3] at hq
    have hk : degB q.1.1 ≤ n := by omega
    have hd : degB2 (q.1.2.1,q.1.2.2) = n - degB q.1.1 := by
      dsimp [degB2]
      omega
    have he := congrArg (fun w : BlockSp (degB2 (m := m)) (n - degB q.1.1) =>
      w ⟨(q.1.2.1,q.1.2.2),hd⟩) (K23_firstSlice n v q.1.1 hk)
    rw [LinearMap.mem_ker.mp (hv q.1.1 hk)] at he
    exact he

/-- The 3-copy fiber of degree `n` fibers over the first coordinate. -/
private def firstEquiv (m n : ℕ) :
    {p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ) // degB3 p = n} ≃
      Σ k : {k : Fin m → ℕ // degB k ≤ n},
        {p : (Fin m → ℕ) × (Fin m → ℕ) // degB2 p = n - degB k.1} where
  toFun q := ⟨⟨q.1.1, by have := q.2; dsimp [degB3] at this; omega⟩,
    ⟨(q.1.2.1, q.1.2.2), by have := q.2; dsimp [degB3, degB2] at *; omega⟩⟩
  invFun s := firstSliceIndex n s.1.1 s.1.2 s.2
  left_inv q := by
    apply Subtype.ext
    dsimp [firstSliceIndex]
  right_inv s := by
    rcases s with ⟨k, q⟩
    dsimp [firstSliceIndex]

/-- Block inner products decompose over first-coordinate slices. -/
private lemma inner_first (n : ℕ) (x y : BlockSp (degB3 (m := m)) n) :
    ⟪x, y⟫_ℂ = ∑ k : {k : Fin m → ℕ // degB k ≤ n},
      ⟪firstSliceBlock n x k.1 k.2, firstSliceBlock n y k.1 k.2⟫_ℂ := by
  classical
  rw [show ⟪x, y⟫_ℂ = ∑ q, ⟪x q, y q⟫_ℂ from PiLp.inner_apply _ _]
  rw [← Fintype.sum_equiv (firstEquiv m n).symm
    (fun s => ⟪x ((firstEquiv m n).symm s), y ((firstEquiv m n).symm s)⟫_ℂ)
    (fun q => ⟪x q, y q⟫_ℂ) (fun s => rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ⟪firstSliceBlock n x k.1 k.2, firstSliceBlock n y k.1 k.2⟫_ℂ
      = ∑ q, ⟪firstSliceBlock n x k.1 k.2 q, firstSliceBlock n y k.1 k.2 q⟫_ℂ from
    PiLp.inner_apply _ _]
  rfl

/-- Slices are linear in the block vector. -/
private lemma firstSliceBlock_sub (n : ℕ) (x y : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    firstSliceBlock n (x - y) k hk
      = firstSliceBlock n x k hk - firstSliceBlock n y k hk := rfl

/-- The slice formula: slices of `q23 (P0B) F` are the projected slices of `F`. -/
private lemma q23_P0B_slice (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    firstSliceBlock n (blockProj degB3 (q23 (P0B m) (P0B_norm_le_one m) F) n) k hk
      = ((LinearMap.ker (lambdaBlock m (n - degB k))).starProjection :
          BlockSp (degB2 (m := m)) (n - degB k) →L[ℂ]
            BlockSp (degB2 (m := m)) (n - degB k))
        (firstSliceBlock n (blockProj degB3 F n) k hk) := by
  classical
  ext q
  have h1 : firstSliceBlock n
      (blockProj degB3 (q23 (P0B m) (P0B_norm_le_one m) F) n) k hk q
      = q23 (P0B m) (P0B_norm_le_one m) F (k, q.1.1, q.1.2) := rfl
  have h2 : q23 (P0B m) (P0B_norm_le_one m) F (k, q.1.1, q.1.2)
      = P0B m (sl1 F k) (q.1.1, q.1.2) := by
    have := congrArg (fun v : L2 ((Fin m → ℕ) × (Fin m → ℕ)) => v (q.1.1, q.1.2))
      (sl1_q23 (P0B m) (P0B_norm_le_one m) F k)
    simpa using this
  have hd : degB2 (m := m) (q.1.1, q.1.2) = n - degB k := q.2
  rw [h1, h2, P0B_apply' m (sl1 F k) (q.1.1, q.1.2) hd]
  have h3 : blockProj degB2 (sl1 F k) (n - degB k)
      = firstSliceBlock n (blockProj degB3 F n) k hk := by
    ext r
    rfl
  rw [h3]

/-- The q23-generator identification on blocks. -/
private lemma q23_block (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB3 (q23 (P0B m) (P0B_norm_le_one m) F) n
      = (LinearMap.ker (toBlock3 (K23 m) n)).starProjection
          (blockProj degB3 F n) := by
  classical
  set v := blockProj degB3 F n
  set w := blockProj degB3 (q23 (P0B m) (P0B_norm_le_one m) F) n with hw
  symm
  apply (LinearMap.ker (toBlock3 (K23 m) n)).eq_starProjection_of_mem_of_inner_eq_zero
  · -- membership: every slice of w is a projection output, hence in the slice kernel
    rw [ker_K23_firstSlices]
    intro k hk
    rw [hw, q23_P0B_slice m F n k hk]
    exact Submodule.starProjection_apply_mem _ _
  · -- orthogonality: slicewise
    intro u hu
    rw [inner_first]
    apply Finset.sum_eq_zero
    intro k _
    rw [firstSliceBlock_sub, hw, q23_P0B_slice m F n k.1 k.2]
    exact (LinearMap.ker (lambdaBlock m (n - degB k.1))).starProjection_inner_eq_zero
      (firstSliceBlock n v k.1 k.2) _ ((ker_K23_firstSlices n u).mp hu k.1 k.2)

private lemma K13_lambdaB_entry
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (K13 m (Finsupp.single p 1)) q =
      (lambdaB m (Finsupp.single (p.1,p.2.2) 1)) (q.1,q.2.2) *
        (Finsupp.single p.2.1 (1 : ℂ)) q.2.1 := by
  classical
  simp only [K13, lambdaB, LinearMap.smul_apply, LinearMap.sum_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul, mul_assoc,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, copy3, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private def secondSliceIndex (n : ℕ) (k : Fin m → ℕ) (hk : degB k ≤ n)
    (q : {p // degB2 (m := m) p = n - degB k}) : {p // degB3 (m := m) p = n} :=
  ⟨(q.1.1,k,q.1.2), by have := q.2; dsimp [degB3, degB2] at *; omega⟩

private def secondSliceBlock (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) : BlockSp (degB2 (m := m)) (n - degB k) :=
  WithLp.toLp 2 (fun q => v (secondSliceIndex n k hk q))

private lemma K13_secondSlice (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    secondSliceBlock n (toBlock3 (K13 m) n v) k hk =
      lambdaBlock m (n - degB k) (secondSliceBlock n v k hk) := by
  classical
  ext q
  have hm (T : FA3 m →ₗ[ℂ] FA3 m) (r : {p // degB3 p = n}) :
      toBlock3 T n v r = ∑ p : {p // degB3 p = n},
        v p * (T (Finsupp.single p.1 1)) r.1 := by
    change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) r.1 = _
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  change toBlock3 (K13 m) n v (secondSliceIndex n k hk q) = _
  rw [hm, lambdaBlock, toBlock2_apply]
  simp_rw [K13_lambdaB_entry]
  symm
  apply Fintype.sum_of_injective (secondSliceIndex n k hk)
  · intro a b h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p => p.1.1) h) (congrArg (fun p => p.1.2.2) h)
  · intro p hp
    have hne : p.1.2.1 ≠ k := by
      intro he
      apply hp
      have hd : degB2 (p.1.1,p.1.2.2) = n - degB k := by
        have := p.2
        dsimp [degB3] at this
        rw [he] at this
        dsimp [degB2]
        omega
      refine ⟨⟨(p.1.1,p.1.2.2),hd⟩, ?_⟩
      apply Subtype.ext
      dsimp [secondSliceIndex]
      exact Prod.ext rfl (Prod.ext he.symm rfl)
    simp [secondSliceIndex, hne]
  · intro p
    simp [secondSliceIndex, secondSliceBlock]

private lemma ker_K13_secondSlices (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    v ∈ LinearMap.ker (toBlock3 (K13 m) n) ↔
      ∀ (k : Fin m → ℕ) (hk : degB k ≤ n),
        secondSliceBlock n v k hk ∈ LinearMap.ker (lambdaBlock m (n - degB k)) := by
  constructor
  · intro hv k hk
    apply LinearMap.mem_ker.mpr
    rw [← K13_secondSlice, LinearMap.mem_ker.mp hv]
    rfl
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext q
    have hq := q.2
    dsimp [degB3] at hq
    have hk : degB q.1.2.1 ≤ n := by omega
    have hd : degB2 (q.1.1,q.1.2.2) = n - degB q.1.2.1 := by
      dsimp [degB2]
      omega
    have he := congrArg (fun w : BlockSp (degB2 (m := m)) (n - degB q.1.2.1) =>
      w ⟨(q.1.1,q.1.2.2),hd⟩) (K13_secondSlice n v q.1.2.1 hk)
    rw [LinearMap.mem_ker.mp (hv q.1.2.1 hk)] at he
    exact he

/-- The 3-copy fiber of degree `n` fibers over the second coordinate. -/
private def secondEquiv (m n : ℕ) :
    {p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ) // degB3 p = n} ≃
      Σ k : {k : Fin m → ℕ // degB k ≤ n},
        {p : (Fin m → ℕ) × (Fin m → ℕ) // degB2 p = n - degB k.1} where
  toFun q := ⟨⟨q.1.2.1, by have := q.2; dsimp [degB3] at this; omega⟩,
    ⟨(q.1.1, q.1.2.2), by have := q.2; dsimp [degB3, degB2] at *; omega⟩⟩
  invFun s := secondSliceIndex n s.1.1 s.1.2 s.2
  left_inv q := by
    apply Subtype.ext
    dsimp [secondSliceIndex]
  right_inv s := by
    rcases s with ⟨k, q⟩
    dsimp [secondSliceIndex]

/-- Block inner products decompose over second-coordinate slices. -/
private lemma inner_second (n : ℕ) (x y : BlockSp (degB3 (m := m)) n) :
    ⟪x, y⟫_ℂ = ∑ k : {k : Fin m → ℕ // degB k ≤ n},
      ⟪secondSliceBlock n x k.1 k.2, secondSliceBlock n y k.1 k.2⟫_ℂ := by
  classical
  rw [show ⟪x, y⟫_ℂ = ∑ q, ⟪x q, y q⟫_ℂ from PiLp.inner_apply _ _]
  rw [← Fintype.sum_equiv (secondEquiv m n).symm
    (fun s => ⟪x ((secondEquiv m n).symm s), y ((secondEquiv m n).symm s)⟫_ℂ)
    (fun q => ⟪x q, y q⟫_ℂ) (fun s => rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ⟪secondSliceBlock n x k.1 k.2, secondSliceBlock n y k.1 k.2⟫_ℂ
      = ∑ q, ⟪secondSliceBlock n x k.1 k.2 q, secondSliceBlock n y k.1 k.2 q⟫_ℂ from
    PiLp.inner_apply _ _]
  rfl

/-- Slices are linear in the block vector. -/
private lemma secondSliceBlock_sub (n : ℕ) (x y : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    secondSliceBlock n (x - y) k hk
      = secondSliceBlock n x k hk - secondSliceBlock n y k hk := rfl

/-- The slice formula: slices of `q13 (P0B) F` are the projected slices of `F`. -/
private lemma q13_P0B_slice (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    secondSliceBlock n (blockProj degB3 (q13 (P0B m) (P0B_norm_le_one m) F) n) k hk
      = ((LinearMap.ker (lambdaBlock m (n - degB k))).starProjection :
          BlockSp (degB2 (m := m)) (n - degB k) →L[ℂ]
            BlockSp (degB2 (m := m)) (n - degB k))
        (secondSliceBlock n (blockProj degB3 F n) k hk) := by
  classical
  ext q
  have h1 : secondSliceBlock n
      (blockProj degB3 (q13 (P0B m) (P0B_norm_le_one m) F) n) k hk q
      = q13 (P0B m) (P0B_norm_le_one m) F (q.1.1, k, q.1.2) := rfl
  have h2 : q13 (P0B m) (P0B_norm_le_one m) F (q.1.1, k, q.1.2)
      = P0B m (sl2 F k) (q.1.1, q.1.2) := by
    have := congrArg (fun v : L2 ((Fin m → ℕ) × (Fin m → ℕ)) => v (q.1.1, q.1.2))
      (sl2_q13 (P0B m) (P0B_norm_le_one m) F k)
    simpa using this
  have hd : degB2 (m := m) (q.1.1, q.1.2) = n - degB k := q.2
  rw [h1, h2, P0B_apply' m (sl2 F k) (q.1.1, q.1.2) hd]
  have h3 : blockProj degB2 (sl2 F k) (n - degB k)
      = secondSliceBlock n (blockProj degB3 F n) k hk := by
    ext r
    rfl
  rw [h3]

/-- The q13-generator identification on blocks. -/
private lemma q13_block (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB3 (q13 (P0B m) (P0B_norm_le_one m) F) n
      = (LinearMap.ker (toBlock3 (K13 m) n)).starProjection
          (blockProj degB3 F n) := by
  classical
  set v := blockProj degB3 F n
  set w := blockProj degB3 (q13 (P0B m) (P0B_norm_le_one m) F) n with hw
  symm
  apply (LinearMap.ker (toBlock3 (K13 m) n)).eq_starProjection_of_mem_of_inner_eq_zero
  · -- membership: every slice of w is a projection output, hence in the slice kernel
    rw [ker_K13_secondSlices]
    intro k hk
    rw [hw, q13_P0B_slice m F n k hk]
    exact Submodule.starProjection_apply_mem _ _
  · -- orthogonality: slicewise
    intro u hu
    rw [inner_second]
    apply Finset.sum_eq_zero
    intro k _
    rw [secondSliceBlock_sub, hw, q13_P0B_slice m F n k.1 k.2]
    exact (LinearMap.ker (lambdaBlock m (n - degB k.1))).starProjection_inner_eq_zero
      (secondSliceBlock n v k.1 k.2) _ ((ker_K13_secondSlices n u).mp hu k.1 k.2)

private lemma toBlock3_neg' (T : FA3 m →ₗ[ℂ] FA3 m) (n : ℕ) :
    toBlock3 (-T) n = -toBlock3 T n := by
  apply LinearMap.ext
  intro v
  ext q
  rfl

private lemma ker_toBlock3_neg (T : FA3 m →ₗ[ℂ] FA3 m) (n : ℕ) :
    LinearMap.ker (toBlock3 (-T) n) = LinearMap.ker (toBlock3 T n) := by
  rw [toBlock3_neg']
  ext v
  simp only [LinearMap.mem_ker, LinearMap.neg_apply, neg_eq_zero]

/-- The spectral input: the three-copy moment identities in `tsum` form plus the
blockwise Kac gap (`kacT_gap` applied to `blockTriple`) yield the Łojasiewicz data at
`α = 7/12`. This is Lemma 3.2 + Lemma 3.3 of the paper on ℓ². -/
theorem lojasiewiczData_P0B (m : ℕ) :
    (lpTensorSquare ((Fin m → ℕ))).LojasiewiczData (P0B m) (7 / 12) := by
  have hblocks : ∀ F n,
      blockProj degB3 (Slp (P0B_norm_le_one m) F) n =
        kacT (blockTriple m n) (blockProj degB3 F n) := by
    intro F n
    have hadd (x y : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
        blockProj degB3 (x + y) n = blockProj degB3 x n + blockProj degB3 y n := rfl
    have hsm (c : ℂ) (x : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
        blockProj degB3 (c • x) n = c • blockProj degB3 x n := rfl
    change blockProj degB3 ((3 : ℂ)⁻¹ •
      (q12 (P0B m) (P0B_norm_le_one m) F +
        q13 (P0B m) (P0B_norm_le_one m) F +
        q23 (P0B m) (P0B_norm_le_one m) F)) n =
      (3 : ℂ)⁻¹ •
        ((LinearMap.ker (toBlock3 (K12 m) n)).starProjection (blockProj degB3 F n) +
          (LinearMap.ker (toBlock3 (K23 m) n)).starProjection (blockProj degB3 F n) +
          (LinearMap.ker (toBlock3 (-K13 m) n)).starProjection (blockProj degB3 F n))
    rw [hsm, hadd, hadd, q12_block, q13_block, q23_block, ker_toBlock3_neg]
    rw [add_right_comm]
  apply lojasiewiczData_of_Slp_gap (P0B_norm_le_one m) (P0B_isAcceptance m)
  exact gap_of_blocks _ hblocks

private lemma lambdaB_vacuum (m : ℕ) :
    lambdaB m (Finsupp.single ((fun _ => 0), (fun _ => 0)) 1) = 0 := by
  classical
  simp [lambdaB, aF, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

private lemma degB_eq_zero {p : Fin m → ℕ} (h : degB p = 0) : p = fun _ => 0 := by
  funext j
  have hj : p j ≤ degB p :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

private lemma lambdaBlock_zero (m : ℕ) : lambdaBlock m 0 = 0 := by
  classical
  ext v q
  rw [lambdaBlock, toBlock2_apply]
  apply Finset.sum_eq_zero
  intro p _
  have hp := p.2
  dsimp [degB2] at hp
  have h1 := degB_eq_zero (p := p.1.1) (by omega)
  have h2 := degB_eq_zero (p := p.1.2) (by omega)
  have he : p.1 = ((fun _ => 0), (fun _ => 0)) := Prod.ext h1 h2
  rw [he, lambdaB_vacuum]
  simp

/-- The vacuum is accepted with probability one (the good set is nonempty), making
the `ε ≥ 1/8` case of the main theorem non-vacuous. -/
theorem accProbA_P0B_vacuum (m : ℕ) :
    (lpTensorSquare ((Fin m → ℕ))).accProbA (P0B m)
      (lp.single 2 (fun _ => 0) 1) = 1 := by
  classical
  let v : FockB m := lp.single 2 (fun _ => 0) 1
  let x := (lpTensorSquare (Fin m → ℕ)).tp v v
  have hx (p : (Fin m → ℕ) × (Fin m → ℕ)) :
      x p = (if p.1 = (fun _ => 0) then 1 else 0) *
        (if p.2 = (fun _ => 0) then 1 else 0) := by
    change v p.1 * v p.2 = _
    simp [v, Pi.single_apply]
  have hk (n : ℕ) : blockProj degB2 x n ∈ LinearMap.ker (lambdaBlock m n) := by
    by_cases hn : n = 0
    · subst n
      simp [lambdaBlock_zero]
    · have hz : blockProj degB2 x n = 0 := by
        ext p
        change x p.1 = 0
        rw [hx]
        have hp := p.2
        split_ifs with h1 h2 h2 <;> simp_all [degB2, degB]
      rw [hz]
      exact Submodule.zero_mem _
  have hfix : P0B m x = x := by
    apply lp.ext
    funext p
    change (LinearMap.ker (lambdaBlock m (degB2 p))).starProjection
      (blockProj degB2 x (degB2 p)) ⟨p,rfl⟩ = x p
    rw [(LinearMap.ker (lambdaBlock m (degB2 p))).starProjection_eq_self_iff.mpr (hk _)]
    rfl
  change (⟪x, P0B m x⟫_ℂ).re = 1
  rw [hfix]
  change (⟪(lpTensorSquare (Fin m → ℕ)).tp v v,
    (lpTensorSquare (Fin m → ℕ)).tp v v⟫_ℂ).re = 1
  rw [TensorSquare.inner_tp]
  simp [inner_self_eq_norm_sq_to_K, v]


/-- **thm:main boson mean zero** (Theorem 6.4), kernel form: if the two-copy test
accepts `ψ` with probability `≥ 1 − ε`, then `ψ` has squared overlap `≥ 1 − 8ε` with a
state accepted with probability one. The physical Gaussian-state conclusion
is `schrodinger_meanZero_fidelity_witness` in `PhysicalMeanZeroRobustness.lean`. -/
theorem main_boson_mean_zero {ψ : FockB m} (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hp : 1 - ε ≤ (lpTensorSquare ((Fin m → ℕ))).accProbA (P0B m) ψ) :
    ∃ φ : FockB m, ‖φ‖ = 1 ∧
      (lpTensorSquare ((Fin m → ℕ))).accProbA (P0B m) φ = 1 ∧
      1 - 8 * ε ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  classical
  by_cases hε8 : 8 * ε < 1
  · obtain ⟨φ, hφ, hpφ, hf⟩ :=
      (lpTensorSquare (Fin m → ℕ)).robust_testing_abstract
        (P0B_isAcceptance m) (P0B_norm_le_one m)
        (by norm_num : (0 : ℝ) ≤ 7 / 12) (by norm_num : (7 : ℝ) / 12 < 2 / 3)
        (lojasiewiczData_P0B m) hψ hε0
        (by simpa only [Cgap_seventwelfths] using hε8) hp
    exact ⟨φ, hφ, hpφ, by simpa only [Cgap_seventwelfths] using hf⟩
  · refine ⟨lp.single 2 (fun _ => 0) 1, ?_, accProbA_P0B_vacuum m, ?_⟩
    · simp
    · have := sq_nonneg ‖⟪ψ, (lp.single 2 (fun _ => 0) 1 : FockB m)⟫_ℂ‖
      linarith

/-- **Corollary 6.8, numerical core, mean-zero case**: for `ε`-far inputs,
`n ≥ (8/ε) log(1/δ)` implies the scalar repetition bound `p₀(ψ)^n ≤ δ`. Use the
square of the draft trace-distance threshold for this squared-fidelity deficit `ε`. -/
theorem boson_mean_zero_testing {ψ : FockB m} (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hfar : ∀ φ : FockB m, ‖φ‖ = 1 →
      (lpTensorSquare ((Fin m → ℕ))).accProbA (P0B m) φ = 1 →
      ‖⟪ψ, φ⟫_ℂ‖ ^ 2 ≤ 1 - ε)
    {n : ℕ} (hn : 8 / ε * Real.log (1 / δ) ≤ n) :
    (lpTensorSquare ((Fin m → ℕ))).accProbA (P0B m) ψ ^ n ≤ δ := by
  have hp0 := (lpTensorSquare (Fin m → ℕ)).accProbA_nonneg (P0B_isAcceptance m) ψ
  have hp1 := (lpTensorSquare (Fin m → ℕ)).accProbA_le_one (P0B_isAcceptance m) hψ
  have hp : (lpTensorSquare (Fin m → ℕ)).accProbA (P0B m) ψ ≤ 1 - ε / 8 := by
    by_contra h
    obtain ⟨φ, hφ, hk, hf⟩ := main_boson_mean_zero hψ
      (show 0 ≤ 1 - (lpTensorSquare (Fin m → ℕ)).accProbA (P0B m) ψ by linarith)
      (show 1 - (1 - (lpTensorSquare (Fin m → ℕ)).accProbA (P0B m) ψ) ≤ (lpTensorSquare (Fin m → ℕ)).accProbA (P0B m) ψ by linarith)
    have hfarφ := hfar φ hφ hk
    linarith
  have hb : 0 ≤ 1 - ε / 8 := hp0.trans hp
  have hlog : -(n : ℝ) * (ε / 8) ≤ Real.log δ := by
    have hn' : 8 / ε * (-Real.log δ) ≤ (n : ℝ) := by
      simpa only [one_div, Real.log_inv] using hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt (div_pos hε (by norm_num : (0 : ℝ) < 8)))
    have he : (8 / ε * (-Real.log δ)) * (ε / 8) = -Real.log δ := by
      field_simp
    rw [he] at hm
    linarith
  calc
    (lpTensorSquare (Fin m → ℕ)).accProbA (P0B m) ψ ^ n ≤ (1 - ε / 8) ^ n := pow_le_pow_left₀ hp0 hp n
    _ ≤ (Real.exp (-(ε / 8))) ^ n :=
      pow_le_pow_left₀ hb (Real.one_sub_le_exp_neg (ε / 8)) n
    _ = Real.exp (-(n : ℝ) * (ε / 8)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hlog
    _ = δ := Real.exp_log hδ


end

end GaussianTesting
