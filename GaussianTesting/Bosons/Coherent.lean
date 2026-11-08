module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Main
public import GaussianTesting.Bosons.Modes
public import GaussianTesting.Bosons.CoherentBlocks

@[expose] public section

/-!
# The bosonic coherent-state test (Theorem 6.5, kernel form)

This file proves the robustness bound with constant `C = 4` for the two-copy
coherent-state test.

The test, in kernel form: the two-copy acceptance projection is the orthogonal
projection onto the kernel of the difference-mode number operator
`N₋ = ∑_l b†_l b_l`, `b_l = (a_l⁽¹⁾ − a_l⁽²⁾)/√2` (we use the unnormalised
difference `u = (1,−1)`, which has the same kernel). `QB_eq_conj` identifies this
projection with the conjugated vacuum test `U_{π/4} (1 ⊗ |0⟩⟨0|) U_{π/4}†` in the
Fock model. `NumberCoherent.lean` transports this projection to the physical
test; `PhysicalCoherent.lean` identifies that test's certainty states with
the displaced-vacuum class in Proposition 6.3.

## Projections, moments, and the robustness bound

* Section A: the 2-copy operator `MB`, its blocks `mBlock`, the acceptance
  projection `QB`, `IsAcceptance`.
* Section B: the three-copy bridge — the sliced identification of
  `q12/q13/q23 QB` with the per-block kernel projections of
  `toBlock3 (MopB a) n` (difference-number operators from `Bosons/Modes.lean`).
* Section C (in `Bosons/CoherentBlocks.lean`): the per-block gap at
  `α = 1/2` via `three_projection_gap_of_gram`: Lemma 6.6 (`blockGapQ`).
* Section D: the Łojasiewicz data at `α = 1/2`, and **Theorem 6.5** with
  constant `Cgap (1/2) = 4`, plus the sampling corollary.
-/

namespace GaussianTesting

open Complex ENNReal Finsupp

noncomputable section
open scoped InnerProductSpace
open Finset
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

local notation "⟪" x ", " y "⟫_ℂ" => inner ℂ x y

/-! ### Section A: the two-copy difference-number operator and the test `QB` -/

/-- Unnormalised difference-mode annihilation on two copies. -/
noncomputable def aM2 (l : Fin m) : FA2 m →ₗ[ℂ] FA2 m :=
  copyL (aF l) - copyR (aF l)

/-- Unnormalised difference-mode creation on two copies. -/
noncomputable def adM2 (l : Fin m) : FA2 m →ₗ[ℂ] FA2 m :=
  copyL (adF l) - copyR (adF l)

/-- The two-copy difference-number operator `∑_l (a†₁−a†₂)(a₁−a₂)` (eigenvalues
`2k`; same kernel as the normalised `N₋`). -/
noncomputable def MB (m : ℕ) : FA2 m →ₗ[ℂ] FA2 m :=
  ∑ l, adM2 l ∘ₗ aM2 l

private lemma coh_degB_update (p : Fin m → ℕ) (l : Fin m) (a : ℕ) :
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

private lemma coh_conserves_smul {T : FA2 m →ₗ[ℂ] FA2 m}
    (hT : ConservesDeg2 T) (c : ℂ) : ConservesDeg2 (c • T) := by
  intro p q h
  exact hT p q (Finsupp.support_smul h)

private lemma coh_conserves_sub {S T : FA2 m →ₗ[ℂ] FA2 m}
    (hS : ConservesDeg2 S) (hT : ConservesDeg2 T) : ConservesDeg2 (S - T) := by
  intro p q h
  rcases Finset.mem_union.mp (Finsupp.support_sub h) with h | h
  · exact hS p q h
  · exact hT p q h

private lemma coh_conserves_sum {ι : Type*} (s : Finset ι) (T : ι → FA2 m →ₗ[ℂ] FA2 m)
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

private lemma coh_conserve12f (l : Fin m) :
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
  have h1 := coh_degB_update p.1 l (p.1 l - 1)
  have h2 := coh_degB_update p.2 l (p.2 l + 1)
  dsimp [degB2]
  omega

private lemma coh_conserve12r (l : Fin m) :
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
  have h1 := coh_degB_update p.1 l (p.1 l + 1)
  have h2 := coh_degB_update p.2 l (p.2 l - 1)
  dsimp [degB2]
  omega


private lemma coh_diagL (l : Fin m) (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    (copyL (adF l) ∘ₗ copyL (aF l)) (single p 1) =
      (p.1 l : ℂ) • single p 1 := by
  classical
  by_cases hp : p.1 l = 0
  · simp [copyL, aF, adF, Finsupp.lsum_single, hp]
  · have hpos := Nat.pos_of_ne_zero hp
    have hh : (↑(p.1 l - 1) : ℝ) + 1 = (p.1 l : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hpos
    simp [copyL, aF, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, Function.update_self, Function.update_idem,
      Nat.sub_add_cancel hpos, Function.update_eq_self, hh,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg (p.1 l))]

private lemma coh_diagR (l : Fin m) (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    (copyR (adF l) ∘ₗ copyR (aF l)) (single p 1) =
      (p.2 l : ℂ) • single p 1 := by
  classical
  by_cases hp : p.2 l = 0
  · simp [copyR, aF, adF, Finsupp.lsum_single, hp]
  · have hpos := Nat.pos_of_ne_zero hp
    have hh : (↑(p.2 l - 1) : ℝ) + 1 = (p.2 l : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hpos
    simp [copyR, aF, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, Function.update_self, Function.update_idem,
      Nat.sub_add_cancel hpos, Function.update_eq_self, hh,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg (p.2 l))]

private lemma coh_expand (l : Fin m) :
    adM2 l ∘ₗ aM2 l =
      (copyL (adF l) ∘ₗ copyL (aF l) - copyL (adF l) ∘ₗ copyR (aF l)) -
      (copyL (aF l) ∘ₗ copyR (adF l) - copyR (adF l) ∘ₗ copyR (aF l)) := by
  classical
  apply Finsupp.lhom_ext
  intro p z
  have he : single p z = z • single p 1 := by simp
  rw [he, map_smul, map_smul]
  congr 1
  ext q
  simp [adM2, aM2, LinearMap.comp_sub, LinearMap.sub_comp, copyL, copyR,
    aF, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Function.update_self]
  ring

lemma conservesDeg2_MB (m : ℕ) : ConservesDeg2 (MB m) := by
  classical
  unfold MB
  apply coh_conserves_sum
  intro l _
  rw [coh_expand]
  apply coh_conserves_sub
  · apply coh_conserves_sub
    · intro p q h
      rw [coh_diagL] at h
      exact congrArg degB2 ((Finsupp.mem_support_single _ _ _).mp
        (Finsupp.support_smul h)).1
    · exact coh_conserve12r l
  · apply coh_conserves_sub
    · exact coh_conserve12f l
    · intro p q h
      rw [coh_diagR] at h
      exact congrArg degB2 ((Finsupp.mem_support_single _ _ _).mp
        (Finsupp.support_smul h)).1

private lemma coh_pair_entry12f (l : Fin m)
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

private lemma coh_pair_entry12r (l : Fin m)
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

private lemma coh_pair_adj12 (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copyL (aF l) ∘ₗ copyR (adF l)) (Finsupp.single p 1)) q =
      star (((copyL (adF l) ∘ₗ copyR (aF l)) (Finsupp.single q 1)) p) := by
  rw [coh_pair_entry12f, coh_pair_entry12r]
  rw [aF_entry l p.1 q.1, adF_entry l p.2 q.2]
  simp only [star_mul]
  ring


lemma MB_entry (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (MB m (Finsupp.single p 1)) q = star ((MB m (Finsupp.single q 1)) p) := by
  classical
  simp only [MB, LinearMap.sum_apply, Finsupp.finsetSum_apply, star_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [coh_expand]
  simp only [LinearMap.sub_apply, Finsupp.sub_apply, coh_diagL, coh_diagR,
    Finsupp.smul_apply, smul_eq_mul, star_sub, star_mul]
  have hf := coh_pair_adj12 l p q
  have hr := congrArg star (coh_pair_adj12 l q p)
  simp only [star_star] at hr
  rw [hf, ← hr]
  by_cases h : p = q
  · subst q
    simp
    ring
  · have h' : q ≠ p := Ne.symm h
    simp [h, h']
    ring

/-- The block of `MB` on the total-degree-`n` sector. -/
noncomputable def mBlock (m n : ℕ) :
    BlockSp (degB2 (m := m)) n →ₗ[ℂ] BlockSp (degB2 (m := m)) n :=
  toBlock2 (MB m) n

lemma mBlock_isSymmetric (m n : ℕ) : (mBlock m n).IsSymmetric := by
  exact toBlock2_symmetric (MB m) MB_entry n

/-- The coherent-state acceptance projection: block-diagonal assembly of the
finite kernel projections of the difference-number operator. -/
noncomputable def QB (m : ℕ) : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 →L[ℂ]
    lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 :=
  blockOp (degB2 (m := m))
    (fun n => ((LinearMap.ker (mBlock m n)).starProjection :
        BlockSp (degB2 (m := m)) n →L[ℂ] BlockSp (degB2 (m := m)) n))
    (by intro n v; exact (LinearMap.ker (mBlock m n)).norm_starProjection_apply_le v)

theorem QB_norm_le_one (m : ℕ) : ‖QB m‖ ≤ 1 := by
  unfold QB blockOp
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- `MB` is swap-invariant on entries (the difference mode changes sign, the
number operator doesn't). -/
lemma MB_swap_entry (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (MB m (Finsupp.single (p.2,p.1) 1)) q =
      (MB m (Finsupp.single p 1)) (q.2,q.1) := by
  classical
  simp only [MB, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [coh_expand]
  simp only [LinearMap.sub_apply, Finsupp.sub_apply, coh_diagL, coh_diagR,
    Finsupp.smul_apply, smul_eq_mul, coh_pair_entry12f, coh_pair_entry12r]
  have he : (p.2,p.1) = q ↔ p = (q.2,q.1) := by
    constructor <;> intro h <;> cases h <;> rfl
  simp only [Finsupp.single_apply, he]
  ring

private lemma mBlock_swap (v : BlockSp (degB2 (m := m)) n) :
    mBlock m n (swapBlock m n v) = swapBlock m n (mBlock m n v) := by
  classical
  ext q
  simp only [mBlock]
  change toBlock2 (MB m) n (swapBlock m n v) q =
    (toBlock2 (MB m) n v) (swapFiber m n q)
  simp only [toBlock2_apply]
  change (∑ p, v (swapFiber m n p) * (MB m (Finsupp.single p.1 1)) q.1) =
    (∑ p, v p * (MB m (Finsupp.single p.1 1)) (q.1.2,q.1.1))
  rw [← Equiv.sum_comp (swapFiber m n)
    (fun p => v (swapFiber m n p) * (MB m (Finsupp.single p.1 1)) q.1)]
  simp only [swapFiber, Equiv.coe_fn_mk, MB_swap_entry]

private lemma projection_swap (v : BlockSp (degB2 (m := m)) n) :
    (LinearMap.ker (mBlock m n)).starProjection (swapBlock m n v) =
      swapBlock m n ((LinearMap.ker (mBlock m n)).starProjection v) := by
  let K := LinearMap.ker (mBlock m n)
  have preserve {w : BlockSp (degB2 (m := m)) n} (hw : w ∈ K) :
      swapBlock m n w ∈ K := by
    change mBlock m n (swapBlock m n w) = 0
    rw [mBlock_swap, LinearMap.mem_ker.mp hw, map_zero]
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
    (preserve (K.starProjection_apply_mem v))
  intro w hw
  have hz := K.starProjection_inner_eq_zero v (swapBlock m n w) (preserve hw)
  have hi := swapBlock_inner (v - K.starProjection v) (swapBlock m n w)
  rw [swapBlock_sq, map_sub] at hi
  exact hi.trans hz


theorem QB_isAcceptance (m : ℕ) :
    (lpTensorSquare ((Fin m → ℕ))).IsAcceptance (QB m) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact blockOp_symmetric _ _ _ (fun n =>
      (LinearMap.ker (mBlock m n)).starProjection_isSymmetric)
  · apply blockOp_idem
    intro n
    apply LinearMap.ext
    intro v
    exact (LinearMap.ker (mBlock m n)).starProjection_eq_self_iff.mpr
      ((LinearMap.ker (mBlock m n)).starProjection_apply_mem v)
  · intro f
    apply lp.ext
    funext p
    change QB m ((lpTensorSquare (Fin m → ℕ)).swap f) p = QB m f (p.2,p.1)
    have happ (g : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
        (q : (Fin m → ℕ) × (Fin m → ℕ)) {n : ℕ} (hq : degB2 q = n) :
        QB m g q = (LinearMap.ker (mBlock m n)).starProjection
          (blockProj degB2 g n) ⟨q,hq⟩ := by subst n; rfl
    rw [happ _ p rfl, blockProj_swap, projection_swap,
      happ f (p.2,p.1) (n := degB2 p) (by simp [degB2, Nat.add_comm])]
    rfl

/-! ### Section B: the three-copy bridge -/

/-- Entry bridge for the pair (1,2): `MopB 0` acts as `MB` on the first two
coordinates with the third as spectator. -/
lemma MopB0_MB_entry (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (MopB 0 (Finsupp.single p 1)) q =
      (MB m (Finsupp.single (p.1,p.2.1) 1)) (q.1,q.2.1) *
        (Finsupp.single p.2.2 (1 : ℂ)) q.2.2 := by
  classical
  simp only [MopB, Mnum, MB, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  norm_num [Adm, Am, uVec, adM2, aM2, LinearMap.comp_sub, LinearMap.sub_comp]
  simp [copy1, copy2, copyL, copyR, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  all_goals ring

/-- Entry bridge for the pair (1,3): spectator = second coordinate. -/
lemma MopB1_MB_entry (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (MopB 1 (Finsupp.single p 1)) q =
      (MB m (Finsupp.single (p.1,p.2.2) 1)) (q.1,q.2.2) *
        (Finsupp.single p.2.1 (1 : ℂ)) q.2.1 := by
  classical
  simp only [MopB, Mnum, MB, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  norm_num [Adm, Am, uVec, adM2, aM2, LinearMap.comp_sub, LinearMap.sub_comp]
  simp [copy1, copy3, copyL, copyR, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  all_goals ring

/-- Entry bridge for the pair (2,3): spectator = first coordinate. -/
lemma MopB2_MB_entry (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (MopB 2 (Finsupp.single p 1)) q =
      (MB m (Finsupp.single (p.2.1,p.2.2) 1)) (q.2.1,q.2.2) *
        (Finsupp.single p.1 (1 : ℂ)) q.1 := by
  classical
  simp only [MopB, Mnum, MB, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  norm_num [Adm, Am, uVec, adM2, aM2, LinearMap.comp_sub, LinearMap.sub_comp]
  simp [copy2, copy3, copyL, copyR, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  all_goals ring

/-- Third-coordinate slices of the `MopB 0` block act as `mBlock`. -/
lemma MopB0_thirdSlice (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    thirdSliceBlock n (toBlock3 (MopB 0) n v) k hk =
      mBlock m (n - degB k) (thirdSliceBlock n v k hk) := by
  classical
  ext q
  have hm (T : FA3 m →ₗ[ℂ] FA3 m) (r : {p // degB3 p = n}) :
      toBlock3 T n v r = ∑ p : {p // degB3 p = n},
        v p * (T (Finsupp.single p.1 1)) r.1 := by
    change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) r.1 = _
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  change toBlock3 (MopB 0) n v (thirdSliceIndex n k hk q) = _
  rw [hm, mBlock, toBlock2_apply]
  simp_rw [MopB0_MB_entry]
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

/-- Kernel of the `MopB 0` block = slicewise kernels of `mBlock`. -/
private lemma ker_MopB0_thirdSlices_mem (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    v ∈ LinearMap.ker (toBlock3 (MopB 0) n) ↔
      ∀ (k : Fin m → ℕ) (hk : degB k ≤ n),
        thirdSliceBlock n v k hk ∈ LinearMap.ker (mBlock m (n - degB k)) := by
  constructor
  · intro hv k hk
    apply LinearMap.mem_ker.mpr
    rw [← MopB0_thirdSlice, LinearMap.mem_ker.mp hv]
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
      w ⟨(q.1.1,q.1.2.1),hd⟩) (MopB0_thirdSlice n v q.1.2.2 hk)
    rw [LinearMap.mem_ker.mp (hv q.1.2.2 hk)] at he
    exact he

lemma ker_MopB0_thirdSlices (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    toBlock3 (MopB 0) n v = 0 ↔
      ∀ (k : Fin m → ℕ) (hk : degB k ≤ n),
        thirdSliceBlock n v k hk ∈ LinearMap.ker (mBlock m (n - degB k)) := by
  exact ker_MopB0_thirdSlices_mem n v

/-- The q12-generator identification on blocks for the coherent test. -/
private lemma QB_apply' (m : ℕ) (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
    {n : ℕ} (i : (Fin m → ℕ) × (Fin m → ℕ)) (h : degB2 i = n) :
    QB m f i = ((LinearMap.ker (mBlock m n)).starProjection :
        BlockSp (degB2 (m := m)) n →L[ℂ] BlockSp (degB2 (m := m)) n)
      (blockProj degB2 f n) ⟨i, h⟩ := by
  subst h
  exact blockOp_apply _ _ _ f i

private lemma q12_QB_slice (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    thirdSliceBlock n (blockProj degB3 (q12 (QB m) (QB_norm_le_one m) F) n) k hk
      = ((LinearMap.ker (mBlock m (n - degB k))).starProjection :
          BlockSp (degB2 (m := m)) (n - degB k) →L[ℂ]
            BlockSp (degB2 (m := m)) (n - degB k))
        (thirdSliceBlock n (blockProj degB3 F n) k hk) := by
  classical
  ext q
  have h1 : thirdSliceBlock n
      (blockProj degB3 (q12 (QB m) (QB_norm_le_one m) F) n) k hk q
      = q12 (QB m) (QB_norm_le_one m) F (q.1.1, q.1.2, k) := rfl
  have h2 : q12 (QB m) (QB_norm_le_one m) F (q.1.1, q.1.2, k)
      = QB m (sl3 F k) (q.1.1, q.1.2) := by
    have := congrArg (fun v : L2 ((Fin m → ℕ) × (Fin m → ℕ)) => v (q.1.1, q.1.2))
      (sl3_q12 (QB m) (QB_norm_le_one m) F k)
    simpa using this
  have hd : degB2 (m := m) (q.1.1, q.1.2) = n - degB k := q.2
  rw [h1, h2, QB_apply' m (sl3 F k) (q.1.1, q.1.2) hd]
  have h3 : blockProj degB2 (sl3 F k) (n - degB k)
      = thirdSliceBlock n (blockProj degB3 F n) k hk := by
    ext r
    rfl
  rw [h3]

lemma q12_blockQ (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB3 (q12 (QB m) (QB_norm_le_one m) F) n
      = (LinearMap.ker (toBlock3 (MopB 0) n)).starProjection
          (blockProj degB3 F n) := by
  classical
  set v := blockProj degB3 F n
  set w := blockProj degB3 (q12 (QB m) (QB_norm_le_one m) F) n with hw
  symm
  apply (LinearMap.ker (toBlock3 (MopB 0) n)).eq_starProjection_of_mem_of_inner_eq_zero
  · -- membership: every slice of w is a projection output, hence in the slice kernel
    rw [ker_MopB0_thirdSlices_mem]
    intro k hk
    rw [hw, q12_QB_slice m F n k hk]
    exact Submodule.starProjection_apply_mem _ _
  · -- orthogonality: slicewise
    intro u hu
    rw [inner_third]
    apply Finset.sum_eq_zero
    intro k _
    rw [thirdSliceBlock_sub, hw, q12_QB_slice m F n k.1 k.2]
    exact (LinearMap.ker (mBlock m (n - degB k.1))).starProjection_inner_eq_zero
      (thirdSliceBlock n v k.1 k.2) _ ((ker_MopB0_thirdSlices_mem n u).mp hu k.1 k.2)

/-- The q13-generator identification on blocks for the coherent test. -/
private def secondSliceIndex (n : ℕ) (k : Fin m → ℕ) (hk : degB k ≤ n)
    (q : {p // degB2 (m := m) p = n - degB k}) : {p // degB3 (m := m) p = n} :=
  ⟨(q.1.1,k,q.1.2), by have := q.2; dsimp [degB3, degB2] at *; omega⟩

private def secondSliceBlock (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) : BlockSp (degB2 (m := m)) (n - degB k) :=
  WithLp.toLp 2 (fun q => v (secondSliceIndex n k hk q))

private lemma K13_secondSlice (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    secondSliceBlock n (toBlock3 (MopB 1) n v) k hk =
      mBlock m (n - degB k) (secondSliceBlock n v k hk) := by
  classical
  ext q
  have hm (T : FA3 m →ₗ[ℂ] FA3 m) (r : {p // degB3 p = n}) :
      toBlock3 T n v r = ∑ p : {p // degB3 p = n},
        v p * (T (Finsupp.single p.1 1)) r.1 := by
    change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) r.1 = _
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  change toBlock3 (MopB 1) n v (secondSliceIndex n k hk q) = _
  rw [hm, mBlock, toBlock2_apply]
  simp_rw [MopB1_MB_entry]
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
    v ∈ LinearMap.ker (toBlock3 (MopB 1) n) ↔
      ∀ (k : Fin m → ℕ) (hk : degB k ≤ n),
        secondSliceBlock n v k hk ∈ LinearMap.ker (mBlock m (n - degB k)) := by
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

/-- The slice formula: slices of `q13 (QB) F` are the projected slices of `F`. -/
private lemma q13_QB_slice (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    secondSliceBlock n (blockProj degB3 (q13 (QB m) (QB_norm_le_one m) F) n) k hk
      = ((LinearMap.ker (mBlock m (n - degB k))).starProjection :
          BlockSp (degB2 (m := m)) (n - degB k) →L[ℂ]
            BlockSp (degB2 (m := m)) (n - degB k))
        (secondSliceBlock n (blockProj degB3 F n) k hk) := by
  classical
  ext q
  have h1 : secondSliceBlock n
      (blockProj degB3 (q13 (QB m) (QB_norm_le_one m) F) n) k hk q
      = q13 (QB m) (QB_norm_le_one m) F (q.1.1, k, q.1.2) := rfl
  have h2 : q13 (QB m) (QB_norm_le_one m) F (q.1.1, k, q.1.2)
      = QB m (sl2 F k) (q.1.1, q.1.2) := by
    have := congrArg (fun v : L2 ((Fin m → ℕ) × (Fin m → ℕ)) => v (q.1.1, q.1.2))
      (sl2_q13 (QB m) (QB_norm_le_one m) F k)
    simpa using this
  have hd : degB2 (m := m) (q.1.1, q.1.2) = n - degB k := q.2
  rw [h1, h2, QB_apply' m (sl2 F k) (q.1.1, q.1.2) hd]
  have h3 : blockProj degB2 (sl2 F k) (n - degB k)
      = secondSliceBlock n (blockProj degB3 F n) k hk := by
    ext r
    rfl
  rw [h3]

lemma q13_blockQ (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB3 (q13 (QB m) (QB_norm_le_one m) F) n
      = (LinearMap.ker (toBlock3 (MopB 1) n)).starProjection
          (blockProj degB3 F n) := by
  classical
  set v := blockProj degB3 F n
  set w := blockProj degB3 (q13 (QB m) (QB_norm_le_one m) F) n with hw
  symm
  apply (LinearMap.ker (toBlock3 (MopB 1) n)).eq_starProjection_of_mem_of_inner_eq_zero
  · -- membership: every slice of w is a projection output, hence in the slice kernel
    rw [ker_K13_secondSlices]
    intro k hk
    rw [hw, q13_QB_slice m F n k hk]
    exact Submodule.starProjection_apply_mem _ _
  · -- orthogonality: slicewise
    intro u hu
    rw [inner_second]
    apply Finset.sum_eq_zero
    intro k _
    rw [secondSliceBlock_sub, hw, q13_QB_slice m F n k.1 k.2]
    exact (LinearMap.ker (mBlock m (n - degB k.1))).starProjection_inner_eq_zero
      (secondSliceBlock n v k.1 k.2) _ ((ker_K13_secondSlices n u).mp hu k.1 k.2)

/-- The q23-generator identification on blocks for the coherent test. -/
private def firstSliceIndex (n : ℕ) (k : Fin m → ℕ) (hk : degB k ≤ n)
    (q : {p // degB2 (m := m) p = n - degB k}) : {p // degB3 (m := m) p = n} :=
  ⟨(k,q.1.1,q.1.2), by have := q.2; dsimp [degB3, degB2] at *; omega⟩

private def firstSliceBlock (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) : BlockSp (degB2 (m := m)) (n - degB k) :=
  WithLp.toLp 2 (fun q => v (firstSliceIndex n k hk q))

private lemma K23_firstSlice (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    firstSliceBlock n (toBlock3 (MopB 2) n v) k hk =
      mBlock m (n - degB k) (firstSliceBlock n v k hk) := by
  classical
  ext q
  have hm (T : FA3 m →ₗ[ℂ] FA3 m) (r : {p // degB3 p = n}) :
      toBlock3 T n v r = ∑ p : {p // degB3 p = n},
        v p * (T (Finsupp.single p.1 1)) r.1 := by
    change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) r.1 = _
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul]
  change toBlock3 (MopB 2) n v (firstSliceIndex n k hk q) = _
  rw [hm, mBlock, toBlock2_apply]
  simp_rw [MopB2_MB_entry]
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
    v ∈ LinearMap.ker (toBlock3 (MopB 2) n) ↔
      ∀ (k : Fin m → ℕ) (hk : degB k ≤ n),
        firstSliceBlock n v k hk ∈ LinearMap.ker (mBlock m (n - degB k)) := by
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

/-- The slice formula: slices of `q23 (QB) F` are the projected slices of `F`. -/
private lemma q23_QB_slice (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ)
    (k : Fin m → ℕ) (hk : degB k ≤ n) :
    firstSliceBlock n (blockProj degB3 (q23 (QB m) (QB_norm_le_one m) F) n) k hk
      = ((LinearMap.ker (mBlock m (n - degB k))).starProjection :
          BlockSp (degB2 (m := m)) (n - degB k) →L[ℂ]
            BlockSp (degB2 (m := m)) (n - degB k))
        (firstSliceBlock n (blockProj degB3 F n) k hk) := by
  classical
  ext q
  have h1 : firstSliceBlock n
      (blockProj degB3 (q23 (QB m) (QB_norm_le_one m) F) n) k hk q
      = q23 (QB m) (QB_norm_le_one m) F (k, q.1.1, q.1.2) := rfl
  have h2 : q23 (QB m) (QB_norm_le_one m) F (k, q.1.1, q.1.2)
      = QB m (sl1 F k) (q.1.1, q.1.2) := by
    have := congrArg (fun v : L2 ((Fin m → ℕ) × (Fin m → ℕ)) => v (q.1.1, q.1.2))
      (sl1_q23 (QB m) (QB_norm_le_one m) F k)
    simpa using this
  have hd : degB2 (m := m) (q.1.1, q.1.2) = n - degB k := q.2
  rw [h1, h2, QB_apply' m (sl1 F k) (q.1.1, q.1.2) hd]
  have h3 : blockProj degB2 (sl1 F k) (n - degB k)
      = firstSliceBlock n (blockProj degB3 F n) k hk := by
    ext r
    rfl
  rw [h3]

lemma q23_blockQ (m : ℕ)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB3 (q23 (QB m) (QB_norm_le_one m) F) n
      = (LinearMap.ker (toBlock3 (MopB 2) n)).starProjection
          (blockProj degB3 F n) := by
  classical
  set v := blockProj degB3 F n
  set w := blockProj degB3 (q23 (QB m) (QB_norm_le_one m) F) n with hw
  symm
  apply (LinearMap.ker (toBlock3 (MopB 2) n)).eq_starProjection_of_mem_of_inner_eq_zero
  · -- membership: every slice of w is a projection output, hence in the slice kernel
    rw [ker_K23_firstSlices]
    intro k hk
    rw [hw, q23_QB_slice m F n k hk]
    exact Submodule.starProjection_apply_mem _ _
  · -- orthogonality: slicewise
    intro u hu
    rw [inner_first]
    apply Finset.sum_eq_zero
    intro k _
    rw [firstSliceBlock_sub, hw, q23_QB_slice m F n k.1 k.2]
    exact (LinearMap.ker (mBlock m (n - degB k.1))).starProjection_inner_eq_zero
      (firstSliceBlock n v k.1 k.2) _ ((ker_K23_firstSlices n u).mp hu k.1 k.2)

/-! ### Section D: Łojasiewicz data and Theorem 6.5 -/

/-- Parametric block-assembly of a quadratic-form gap (generalises the `7/12`
version used for the mean-zero test). -/
lemma gap_of_blocks_param {α : ℝ}
    (S : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) →L[ℂ]
      L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)))
    (Tn : ∀ n, BlockSp (degB3 (m := m)) n →ₗ[ℂ] BlockSp (degB3 (m := m)) n)
    (hS : ∀ F n, blockProj degB3 (S F) n = Tn n (blockProj degB3 F n))
    (hgap : ∀ n w, 0 ≤ (⟪w, (((Tn n) - LinearMap.id) ∘ₗ
      ((Tn n) - ((α : ℝ) : ℂ) • LinearMap.id)) w⟫_ℂ).re)
    (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
    0 ≤ (⟪F, S (S F)⟫_ℂ - (1 + (α : ℝ)) * ⟪F, S F⟫_ℂ +
      (α : ℝ) * ⟪F,F⟫_ℂ).re := by
  let a : ℂ := ((α : ℝ) : ℂ)
  let G := S (S F) - (1 + a) • S F + a • F
  have he : ⟪F,G⟫_ℂ = ⟪F,S (S F)⟫_ℂ - (1+a) * ⟪F,S F⟫_ℂ + a * ⟪F,F⟫_ℂ := by
    simp only [G, inner_add_right, inner_sub_right, inner_smul_right]
  change 0 ≤ (⟪F,S (S F)⟫_ℂ - (1+a) * ⟪F,S F⟫_ℂ + a * ⟪F,F⟫_ℂ).re
  rw [← he, inner_blocks degB3 F G,
    Complex.re_tsum (summable_inner_blocks degB3 F G)]
  apply tsum_nonneg
  intro n
  have hb : blockProj degB3 G n =
      ((Tn n - LinearMap.id) ∘ₗ
        (Tn n - a • LinearMap.id)) (blockProj degB3 F n) := by
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
  exact hgap n (blockProj degB3 F n)

/-- Polynomial-gap form of draft Lemma 6.6 (`lem:S-spectrum-coherent-states`) for the coherent-state test.
For its three-copy average `S`, the form of `(S - I)(S - (1/2)I)` is nonnegative
on every vector in the full three-copy Fock space. -/
theorem coherent_polynomial_gap (m : ℕ) (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
    0 ≤ (⟪F, Slp (QB_norm_le_one m) (Slp (QB_norm_le_one m) F)⟫_ℂ -
      (1 + (1 / 2 : ℝ)) * ⟪F, Slp (QB_norm_le_one m) F⟫_ℂ +
      (1 / 2 : ℝ) * ⟪F, F⟫_ℂ).re := by
  have hblocks : ∀ F n,
      blockProj degB3 (Slp (QB_norm_le_one m) F) n =
        Tq3 m n (blockProj degB3 F n) := by
    intro F n
    have hadd (x y : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
        blockProj degB3 (x + y) n = blockProj degB3 x n + blockProj degB3 y n := rfl
    have hsm (c : ℂ) (x : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
        blockProj degB3 (c • x) n = c • blockProj degB3 x n := rfl
    change blockProj degB3 ((3 : ℂ)⁻¹ •
      (q12 (QB m) (QB_norm_le_one m) F +
        q13 (QB m) (QB_norm_le_one m) F +
        q23 (QB m) (QB_norm_le_one m) F)) n = _
    rw [hsm, hadd, hadd, q12_blockQ, q13_blockQ, q23_blockQ]
    rfl
  exact gap_of_blocks_param _ (Tq3 m) hblocks blockGapQ F

/-- The Łojasiewicz data for the coherent-state test at `α = 1/2`
(Lemma 3.2 + Lemma 3.3 + Lemma 6.6 on ℓ²). -/
theorem lojasiewiczData_QB (m : ℕ) :
    (lpTensorSquare ((Fin m → ℕ))).LojasiewiczData (QB m) (1 / 2) :=
  lojasiewiczData_of_Slp_gap (QB_norm_le_one m) (QB_isAcceptance m) (coherent_polynomial_gap m)

/-- The vacuum is accepted with certainty. -/
private lemma MB_vacuum (m : ℕ) :
    MB m (Finsupp.single ((fun _ => 0), (fun _ => 0)) 1) = 0 := by
  classical
  simp [MB, aM2, adM2, copyL, copyR, aF, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

private lemma degB_eq_zero {p : Fin m → ℕ} (h : degB p = 0) : p = fun _ => 0 := by
  funext j
  have hj : p j ≤ degB p :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

private lemma mBlock_zero (m : ℕ) : mBlock m 0 = 0 := by
  classical
  ext v q
  rw [mBlock, toBlock2_apply]
  apply Finset.sum_eq_zero
  intro p _
  have hp := p.2
  dsimp [degB2] at hp
  have h1 := degB_eq_zero (p := p.1.1) (by omega)
  have h2 := degB_eq_zero (p := p.1.2) (by omega)
  have he : p.1 = ((fun _ => 0), (fun _ => 0)) := Prod.ext h1 h2
  rw [he, MB_vacuum]
  simp

theorem accProbA_QB_vacuum (m : ℕ) :
    (lpTensorSquare ((Fin m → ℕ))).accProbA (QB m)
      (lp.single 2 (fun _ => 0) 1) = 1 := by
  classical
  let v : FockB m := lp.single 2 (fun _ => 0) 1
  let x := (lpTensorSquare (Fin m → ℕ)).tp v v
  have hx (p : (Fin m → ℕ) × (Fin m → ℕ)) :
      x p = (if p.1 = (fun _ => 0) then 1 else 0) *
        (if p.2 = (fun _ => 0) then 1 else 0) := by
    change v p.1 * v p.2 = _
    simp [v, Pi.single_apply]
  have hk (n : ℕ) : blockProj degB2 x n ∈ LinearMap.ker (mBlock m n) := by
    by_cases hn : n = 0
    · subst n
      simp [mBlock_zero]
    · have hz : blockProj degB2 x n = 0 := by
        ext p
        change x p.1 = 0
        rw [hx]
        have hp := p.2
        split_ifs with h1 h2 h2 <;> simp_all [degB2, degB]
      rw [hz]
      exact Submodule.zero_mem _
  have hfix : QB m x = x := by
    apply lp.ext
    funext p
    change (LinearMap.ker (mBlock m (degB2 p))).starProjection
      (blockProj degB2 x (degB2 p)) ⟨p,rfl⟩ = x p
    rw [(LinearMap.ker (mBlock m (degB2 p))).starProjection_eq_self_iff.mpr (hk _)]
    rfl
  change (⟪x, QB m x⟫_ℂ).re = 1
  rw [hfix]
  change (⟪(lpTensorSquare (Fin m → ℕ)).tp v v,
    (lpTensorSquare (Fin m → ℕ)).tp v v⟫_ℂ).re = 1
  rw [TensorSquare.inner_tp]
  simp [inner_self_eq_norm_sq_to_K, v]

lemma Cgap_half : Cgap (1 / 2) = 4 := by
  norm_num [Cgap]

/-- **thm:main boson coherent** (Theorem 6.5), kernel form: if the two-copy
coherent-state test accepts `ψ` with probability `≥ 1 − ε`, then `ψ` has
squared overlap `≥ 1 − 4ε` with a state accepted with probability one.
The manuscript's physical coherent-state conclusion is proved in
`PhysicalCoherentRobustness.lean`. -/
theorem main_boson_coherent {ψ : FockB m} (hψ : ‖ψ‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hp : 1 - ε ≤ (lpTensorSquare ((Fin m → ℕ))).accProbA (QB m) ψ) :
    ∃ φ : FockB m, ‖φ‖ = 1 ∧
      (lpTensorSquare ((Fin m → ℕ))).accProbA (QB m) φ = 1 ∧
      1 - 4 * ε ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  classical
  by_cases hε4 : 4 * ε < 1
  · obtain ⟨φ, hφ, hpφ, hf⟩ :=
      (lpTensorSquare (Fin m → ℕ)).robust_testing_abstract
        (QB_isAcceptance m) (QB_norm_le_one m)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 2 / 3)
        (lojasiewiczData_QB m) hψ hε0
        (by simpa only [Cgap_half] using hε4) hp
    exact ⟨φ, hφ, hpφ, by simpa only [Cgap_half] using hf⟩
  · refine ⟨lp.single 2 (fun _ => 0) 1, ?_, accProbA_QB_vacuum m, ?_⟩
    · simp
    · have := sq_nonneg ‖⟪ψ, (lp.single 2 (fun _ => 0) 1 : FockB m)⟫_ℂ‖
      linarith

/-- **Corollary 6.8, numerical core, coherent case**: for `ε`-far inputs,
`n ≥ (4/ε) log(1/δ)` implies `q(ψ)^n ≤ δ`. Here `ε` is the square of the
draft trace-distance threshold when applying this theorem to Corollary 6.8. -/
theorem boson_coherent_testing {ψ : FockB m} (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hfar : ∀ φ : FockB m, ‖φ‖ = 1 →
      (lpTensorSquare ((Fin m → ℕ))).accProbA (QB m) φ = 1 →
      ‖⟪ψ, φ⟫_ℂ‖ ^ 2 ≤ 1 - ε)
    {n : ℕ} (hn : 4 / ε * Real.log (1 / δ) ≤ n) :
    (lpTensorSquare ((Fin m → ℕ))).accProbA (QB m) ψ ^ n ≤ δ := by
  have hp0 := (lpTensorSquare (Fin m → ℕ)).accProbA_nonneg (QB_isAcceptance m) ψ
  have hp1 := (lpTensorSquare (Fin m → ℕ)).accProbA_le_one (QB_isAcceptance m) hψ
  have hp : (lpTensorSquare (Fin m → ℕ)).accProbA (QB m) ψ ≤ 1 - ε / 4 := by
    by_contra h
    obtain ⟨φ, hφ, hk, hf⟩ := main_boson_coherent hψ
      (show 0 ≤ 1 - (lpTensorSquare (Fin m → ℕ)).accProbA (QB m) ψ by linarith)
      (show 1 - (1 - (lpTensorSquare (Fin m → ℕ)).accProbA (QB m) ψ) ≤ (lpTensorSquare (Fin m → ℕ)).accProbA (QB m) ψ by linarith)
    have hfarφ := hfar φ hφ hk
    linarith
  have hb : 0 ≤ 1 - ε / 4 := hp0.trans hp
  have hlog : -(n : ℝ) * (ε / 4) ≤ Real.log δ := by
    have hn' : 4 / ε * (-Real.log δ) ≤ (n : ℝ) := by
      simpa only [one_div, Real.log_inv] using hn
    have hm := mul_le_mul_of_nonneg_right hn' (le_of_lt (div_pos hε (by norm_num : (0 : ℝ) < 4)))
    have he : (4 / ε * (-Real.log δ)) * (ε / 4) = -Real.log δ := by
      field_simp
    rw [he] at hm
    linarith
  calc
    (lpTensorSquare (Fin m → ℕ)).accProbA (QB m) ψ ^ n ≤ (1 - ε / 4) ^ n := pow_le_pow_left₀ hp0 hp n
    _ ≤ (Real.exp (-(ε / 4))) ^ n :=
      pow_le_pow_left₀ hb (Real.one_sub_le_exp_neg (ε / 4)) n
    _ = Real.exp (-(n : ℝ) * (ε / 4)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr hlog
    _ = δ := Real.exp_log hδ

end

end GaussianTesting
