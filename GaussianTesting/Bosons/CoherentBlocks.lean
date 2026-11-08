module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Main
public import GaussianTesting.Bosons.Modes
public import GaussianTesting.Bosons.ThreeProjectionGap
public import GaussianTesting.Bosons.OccupationGram

@[expose] public section

/-!
# Exact occupation-sector spectra in Lemma 6.6

For each total-degree block of the three-copy Fock space, the average of the
three kernel projections of the blocked difference-number operators
`toBlock3 (MopB a) n` satisfies `(T - I)(T - (1/2)I) ≥ 0`. Block assembly in
`Coherent.lean` gives the full-space polynomial inequality; the literal
spectrum-containment wrapper is separate. The working draft labels the result `lem:S-spectrum-coherent-states`.

The rotated-frame creation monomials `gmon (frame a) ![p, q, 0]`
(centre-of-mass exponents `p`, in-plane exponents `q`, difference-slot
exponent `0`) are an orthonormal family spanning the kernel, with cross-frame
Gram entries `(−1/2)^{|q|}`. `blockSpectrumQ_nonzero` identifies the
nonzero spectrum of the actual average with the two Gram eigenvalues
`(1+2*(-1/2)^k)/3` and `(1-(-1/2)^k)/3`, where `k=|q|`.
The cases `k=0,1,2` and strict bound for `k≥3` are proved in
`OccupationGram.lean`. The polynomial inequality used to assemble total-number
blocks is now a consequence of this exact spectral calculation.
-/

namespace GaussianTesting

open Complex Finsupp

variable {m : ℕ}

local notation "⟪" x ", " y "⟫_ℂ" => inner ℂ x y

/-! ### Section C: the per-block gap at `α = 1/2` (Lemma 6.6) -/

/-- The homogeneous-component map into a degree block: forget all coefficients
outside the fiber. -/
noncomputable def homogToBlock (n : ℕ) (f : FA3 m) : BlockSp (degB3 (m := m)) n :=
  WithLp.toLp 2 (fun i => f i.1)

lemma homogToBlock_add (n : ℕ) (f g : FA3 m) :
    homogToBlock n (f + g) = homogToBlock n f + homogToBlock n g := by
  rfl

lemma homogToBlock_smul (n : ℕ) (z : ℂ) (f : FA3 m) :
    homogToBlock n (z • f) = z • homogToBlock n f := by
  rfl

/-- Homogeneous components of the wrong degree vanish in the block. -/
lemma homogToBlock_eq_zero {n d : ℕ} (hnd : d ≠ n) {f : FA3 m}
    (hf : IsHomog3 d f) : homogToBlock n f = 0 := by
  ext i
  change f i.1 = 0
  by_contra h
  exact hnd ((hf i.1 (Finsupp.mem_support_iff.mpr h)).symm.trans i.2)

private lemma fiber_sum {V : Type*} [AddCommMonoid V] {n : ℕ} {f : FA3 m}
    (hf : IsHomog3 n f) (H : ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) → ℂ → V)
    (hH : ∀ i, H i 0 = 0) :
    (∑ i : {i // degB3 i = n}, H i.1 (f i.1)) = f.sum H := by
  classical
  change _ = ∑ i ∈ f.support, H i (f i)
  rw [← Finset.sum_subtype_of_mem (fun i => H i (f i)) hf]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hni
  have hz : f i.1 = 0 := by
    apply Finsupp.notMem_support_iff.mp
    simpa using hni
  exact hz ▸ hH i.1

/-- The block inner product computes the pairing on degree-`n` homogeneous
vectors. -/
lemma inner_homogToBlock {n : ℕ} {f : FA3 m} (hf : IsHomog3 n f) (g : FA3 m) :
    ⟪homogToBlock n f, homogToBlock n g⟫_ℂ = pairF f g := by
  classical
  simpa [PiLp.inner_apply, RCLike.inner_apply, homogToBlock, pairF, mul_comm] using
    fiber_sum hf (fun i z => star z * g i) (by simp)

/-- `toBlock3` intertwines with `homogToBlock` on degree-conserving operators
and homogeneous vectors. -/
lemma toBlock3_homogToBlock {T : FA3 m →ₗ[ℂ] FA3 m} (hT : ConservesDeg3 T)
    {n : ℕ} {f : FA3 m} (hf : IsHomog3 n f) :
    toBlock3 T n (homogToBlock n f) = homogToBlock n (T f) := by
  classical
  have _hconserves : ConservesDeg3 T := hT
  have hdecomp : (∑ i : {i // degB3 i = n}, f i.1 • Finsupp.single i.1 1) = f := by
    rw [fiber_sum hf (fun i z => z • Finsupp.single i 1) (by simp)]
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using f.sum_single
  ext i
  rw [toBlock3_apply]
  change (∑ j : {j // degB3 j = n}, f j.1 * (T (Finsupp.single j.1 1)) i.1) = (T f) i.1
  conv_rhs => rw [← hdecomp]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Exponent pattern of a two-part occupation: `p` on the centre-of-mass slot,
`q` on the in-plane slot, nothing on the difference slot. -/
def expPQ (pq : (Fin m → ℕ) × (Fin m → ℕ)) : Fin 3 → Fin m → ℕ :=
  ![pq.1, pq.2, 0]

/-- The squared norm of the rotated monomial `gmon (frame a) (expPQ pq)`
(independent of the frame `a`). -/
def NrmQ (pq : (Fin m → ℕ) × (Fin m → ℕ)) : ℚ :=
  (∏ l, ((pq.1 l).factorial : ℚ) * 3 ^ (pq.1 l)) *
    ∏ l, ((pq.2 l).factorial : ℚ) * 6 ^ (pq.2 l)

lemma NrmQ_pos (pq : (Fin m → ℕ) × (Fin m → ℕ)) : 0 < NrmQ pq := by
  unfold NrmQ
  apply mul_pos <;> apply Finset.prod_pos <;> intro l hl <;>
    apply mul_pos
  · exact_mod_cast Nat.factorial_pos _
  · positivity
  · exact_mod_cast Nat.factorial_pos _
  · positivity

/-- The normalised rotated-monomial block vectors: the `j`-th vector of the
`a`-th frame family in the degree-`n` block. -/
noncomputable def eVecQ (n : ℕ) (a : Fin 3) (j : {i // degB2 (m := m) i = n}) :
    BlockSp (degB3 (m := m)) n :=
  ((Real.sqrt (NrmQ j.1) : ℂ)⁻¹) •
    homogToBlock n (gmon (frame a) (expPQ j.1))

/-- The cross-Gram weight: `(−1/2)^{|q|}`. -/
noncomputable def sQ (j : {i // degB2 (m := m) i = n}) : ℝ := (-(1/2) : ℝ) ^ degB j.1.2

private lemma expPQ_degree (pq : (Fin m → ℕ) × (Fin m → ℕ)) :
    (∑ s, degB (expPQ pq s)) = degB2 pq := by
  simp [Fin.sum_univ_three, expPQ, degB2, degB]

private lemma expPQ_inj {pq pq' : (Fin m → ℕ) × (Fin m → ℕ)} :
    expPQ pq = expPQ pq' ↔ pq = pq' := by
  constructor
  · intro h
    exact Prod.ext (congrFun h 0) (congrFun h 1)
  · rintro rfl; rfl

private lemma pairF_gmon_frames (a b : Fin 3)
    (pq pq' : (Fin m → ℕ) × (Fin m → ℕ)) :
    pairF (gmon (frame a) (expPQ pq)) (gmon (frame b) (expPQ pq')) =
      if pq = pq' then
        (((if a = b then 1 else (-1/2 : ℚ) ^ degB pq.2) * NrmQ pq : ℚ) : ℂ)
      else 0 := by
  classical
  rw [gram_diag]
  · simp only [expPQ_inj]
    split_ifs with hp hab
    · subst pq'; subst b
      simp [Fin.prod_univ_three, expPQ, frame, NrmQ]
    · subst pq'
      have hd := pairQ_w_w_ne hab
      have hprod : (∏ l, ((pq.2 l).factorial : ℚ) * (-3 : ℚ) ^ pq.2 l) =
          (-1/2 : ℚ) ^ degB pq.2 * ∏ l, ((pq.2 l).factorial : ℚ) * 6 ^ pq.2 l := by
        simp only [degB, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro l hl
        calc
          _ = ((pq.2 l).factorial : ℚ) * ((-1/2 : ℚ) * 6) ^ pq.2 l := by norm_num
          _ = _ := by rw [mul_pow]; ring
      have htotal : (∏ s, ∏ l, ((expPQ pq s l).factorial : ℚ) *
          pairQ (frame a s) (frame b s) ^ expPQ pq s l) =
          (-1/2 : ℚ) ^ degB pq.2 * NrmQ pq := by
        simp [Fin.prod_univ_three, expPQ, frame, hd]
        rw [hprod]
        unfold NrmQ
        ring
      exact_mod_cast htotal
    · rfl
  · intro s t hst hs ht
    fin_cases s <;> fin_cases t <;> simp_all [expPQ, frame]

/-- The Gram matrix of the three frame families (Lemma 6.6's ladder
computation): orthonormal within a frame, `(−1/2)^{|q|}`-diagonal across
frames. -/
lemma gram_eVecQ (n : ℕ) (a b : Fin 3) (j j' : {i // degB2 (m := m) i = n}) :
    ⟪eVecQ n a j, eVecQ n b j'⟫_ℂ =
      if j = j' then (if a = b then 1 else ((sQ j : ℝ) : ℂ)) else 0 := by
  classical
  have hj : IsHomog3 n (gmon (frame a) (expPQ j.1)) := by
    simpa only [expPQ_degree, j.2] using gmon_homog (frame a) (expPQ j.1)
  have hpos : (0 : ℝ) < NrmQ j.1 := by exact_mod_cast NrmQ_pos j.1
  have hr : (Real.sqrt (NrmQ j.1) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hpos))
  have hs : (Real.sqrt (NrmQ j.1) : ℂ) * (Real.sqrt (NrmQ j.1) : ℂ) =
      (NrmQ j.1 : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt hpos.le]
    norm_cast
  unfold eVecQ
  rw [inner_smul_left, inner_smul_right, inner_homogToBlock hj, pairF_gmon_frames]
  by_cases he : j = j'
  · subst j'
    simp only [ite_true, map_inv₀, Complex.conj_ofReal]
    split_ifs with hab
    · simp only [one_mul]
      rw [← hs]
      field_simp
    · simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_neg,
        Rat.cast_one, Rat.cast_ofNat]
      rw [← hs]
      have hc : (sQ j : ℂ) = (-1/2 : ℂ) ^ degB j.1.2 := by
        unfold sQ
        push_cast
        ring
      rw [hc]
      field_simp
  · have hv : j.1 ≠ j'.1 := fun h => he (Subtype.ext h)
    simp [hv, he]

lemma sQ_mem (j : {i // degB2 (m := m) i = n}) :
    sQ j = 1 ∨ (-(1/2) ≤ sQ j ∧ sQ j ≤ 1/4) := by
  by_cases hk : degB j.val.2 = 0
  · left
    simp [sQ, hk]
  · right
    have hmax := coherentSectorMaxEigenvalue_le_half (Nat.pos_of_ne_zero hk)
    have hc := (le_max_left (coherentSectorConstantEigenvalue (degB j.val.2))
      (coherentSectorSumZeroEigenvalue (degB j.val.2))).trans hmax
    have hz := (le_max_right (coherentSectorConstantEigenvalue (degB j.val.2))
      (coherentSectorSumZeroEigenvalue (degB j.val.2))).trans hmax
    dsimp [coherentSectorConstantEigenvalue, coherentSectorSumZeroEigenvalue] at hc hz
    dsimp [sQ]
    constructor <;> linarith

private noncomputable def homogLM (n : ℕ) : FA3 m →ₗ[ℂ] BlockSp (degB3 (m := m)) n where
  toFun := homogToBlock n
  map_add' := homogToBlock_add n
  map_smul' := homogToBlock_smul n

private lemma block_gmon_span (n : ℕ) (a : Fin 3) (v : BlockSp (degB3 (m := m)) n) :
    v ∈ Submodule.span ℂ (Set.range (fun β : Fin 3 → Fin m → ℕ =>
      homogToBlock n (gmon (frame a) β))) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun β : Fin 3 → Fin m → ℕ =>
      homogToBlock n (gmon (frame a) β)))
  have hi (i : {i // degB3 (m := m) i = n}) :
      homogToBlock n (Finsupp.single i.1 1) ∈ S := by
    have hh := single_mem_span_gmon (frame a) (frame_spans a) i.1
    change homogLM n (Finsupp.single i.1 1) ∈ S
    exact Submodule.span_induction
      (p := fun x _ => homogLM n x ∈ S)
      (fun x hx => by obtain ⟨β, rfl⟩ := hx; exact Submodule.subset_span ⟨β, rfl⟩)
      (by simp)
      (fun x y _ _ ix iy => by simpa using S.add_mem ix iy)
      (fun z x _ ix => by simpa using S.smul_mem z ix) hh
  have hv : v = ∑ i, v i • homogToBlock n (Finsupp.single i.1 1) := by
    ext j
    change v j = (∑ i, v i • homogToBlock n (Finsupp.single i.1 1)) j
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [PiLp.smul_apply]
    change v j = ∑ i, v i * (Finsupp.single i.1 (1 : ℂ)) j.1
    simp only [Finsupp.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      rw [ite_eq_right (fun h => hij (Subtype.ext h))]
      simp
    · simp
  rw [hv]
  exact S.sum_mem fun i _ => S.smul_mem _ (hi i)

private lemma block_gmon_eigen (n : ℕ) (a : Fin 3) (β : Fin 3 → Fin m → ℕ) :
    toBlock3 (MopB a) n (homogToBlock n (gmon (frame a) β)) =
      ((2 * degB (β 2) : ℕ) : ℂ) • homogToBlock n (gmon (frame a) β) := by
  classical
  by_cases hd : (∑ s, degB (β s)) = n
  · have hh : IsHomog3 n (gmon (frame a) β) := hd ▸ gmon_homog _ _
    rw [toBlock3_homogToBlock (conservesDeg3_MopB a) hh]
    have he := Mnum_gmon (frame a) β 2 (fun t ht _ => frame_orth a 2 t (Ne.symm ht))
    change Mnum (uVec a) (gmon (frame a) β) = _ at he
    simp only [show frame a 2 = uVec a from rfl, pairQ_u_u_same] at he
    rw [MopB, he, homogToBlock_smul]
    congr 1
    push_cast
    rfl
  · rw [homogToBlock_eq_zero hd (gmon_homog _ _)]
    simp

private lemma eVecQ_mem_ker (n : ℕ) (a : Fin 3)
    (j : {i // degB2 (m := m) i = n}) :
    eVecQ n a j ∈ LinearMap.ker (toBlock3 (MopB a) n) := by
  rw [LinearMap.mem_ker]
  simp only [eVecQ, map_smul, block_gmon_eigen]
  simp [expPQ, degB]

private lemma pairF_single_r (f : FA3 m)
    (q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    pairF f (Finsupp.single q z) = star (f q) * z := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [pairF_add_left, hf, hg, add_mul]
  | single p w =>
    simp [pairF, Finsupp.single_apply, eq_comm]
    split_ifs <;> simp_all

private lemma pairF_conj (f g : FA3 m) : pairF f g = star (pairF g f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [pairF_add_left, pairF_add_right, hf, hf']
  | single p z =>
    rw [pairF_single_r]
    simp [pairF, Finsupp.sum_single_index, mul_comm]

private lemma block_MopB_symm (n : ℕ) (a : Fin 3) :
    (toBlock3 (MopB (m := m) a) n).IsSymmetric := by
  classical
  have hsumL (s : Finset (Fin m)) (F : Fin m → FA3 m) (g : FA3 m) :
      pairF (∑ l ∈ s, F l) g = ∑ l ∈ s, pairF (F l) g := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert l s hl ih => simp [hl, pairF_add_left, ih]
  have hsumR (s : Finset (Fin m)) (F : Fin m → FA3 m) (g : FA3 m) :
      pairF g (∑ l ∈ s, F l) = ∑ l ∈ s, pairF g (F l) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert l s hl ih => simp [hl, pairF_add_right, ih]
  have hadj (f g : FA3 m) : pairF (MopB a f) g = pairF f (MopB a g) := by
    simp only [MopB, Mnum, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [hsumL, hsumR]
    apply Finset.sum_congr rfl
    intro l hl
    rw [pairF_adm, pairF_conj f, pairF_adm, ← pairF_conj]
  apply toBlock3_symmetric
  intro p q
  have hh := hadj (Finsupp.single p 1) (Finsupp.single q 1)
  rw [pairF_single_r] at hh
  simpa [pairF, Finsupp.sum_single_index] using congrArg star hh

private lemma zero_slot_mem (n : ℕ) (a : Fin 3) (β : Fin 3 → Fin m → ℕ)
    (hb : β 2 = 0) :
    homogToBlock n (gmon (frame a) β) ∈ Submodule.span ℂ (Set.range (eVecQ n a)) := by
  classical
  by_cases hd : (∑ s, degB (β s)) = n
  · let pq := (β 0, β 1)
    have he : β = expPQ pq := by
      funext s; fin_cases s <;> simp [expPQ, pq, hb]
    have hp : degB2 pq = n := by rw [← expPQ_degree, ← he]; exact hd
    let j : {i // degB2 (m := m) i = n} := ⟨pq, hp⟩
    have hr : (Real.sqrt (NrmQ pq) : ℂ) ≠ 0 := by
      have hh : (0 : ℝ) < NrmQ pq := by exact_mod_cast NrmQ_pos pq
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hh))
    have hm := (Submodule.span ℂ (Set.range (eVecQ n a))).smul_mem
      (Real.sqrt (NrmQ pq) : ℂ) (Submodule.subset_span (Set.mem_range_self j))
    simpa [eVecQ, j, smul_smul, hr, ← he] using hm
  · rw [homogToBlock_eq_zero hd (gmon_homog _ _)]
    exact Submodule.zero_mem _

/-- The rotated monomials of the `a`-th frame with zero difference-slot
exponent span exactly the kernel of the blocked difference-number operator. -/
lemma ker_MopB_eq_span (n : ℕ) (a : Fin 3) :
    LinearMap.ker (toBlock3 (MopB (m := m) a) n) =
      Submodule.span ℂ (Set.range (eVecQ n a)) := by
  classical
  let S := Submodule.span ℂ (Set.range (eVecQ (m := m) n a))
  have hS : S ≤ LinearMap.ker (toBlock3 (MopB a) n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact eVecQ_mem_ker n a j
  apply le_antisymm
  · intro v hv
    let r := v - S.starProjection v
    have hr : toBlock3 (MopB a) n r = 0 := by
      rw [show r = v - S.starProjection v from rfl, map_sub]
      rw [LinearMap.mem_ker.mp hv,
        LinearMap.mem_ker.mp (hS (S.starProjection_apply_mem v)), sub_self]
    have ho : ∀ β : Fin 3 → Fin m → ℕ,
        ⟪homogToBlock n (gmon (frame a) β), r⟫_ℂ = 0 := by
      intro β
      by_cases hb : β 2 = 0
      · exact inner_eq_zero_symm.mp
          (S.starProjection_inner_eq_zero v _ (zero_slot_mem n a β hb))
      · have hd : degB (β 2) ≠ 0 := by
          intro hz
          apply hb
          funext l
          exact (Finset.sum_eq_zero_iff.mp hz) l (Finset.mem_univ l)
        have hl : ((2 * degB (β 2) : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.mul_ne_zero (by decide : 2 ≠ 0) hd
        have hh := block_MopB_symm n a (homogToBlock n (gmon (frame a) β)) r
        rw [block_gmon_eigen, hr, inner_smul_left, inner_zero_right] at hh
        simp only [map_natCast] at hh
        exact (mul_eq_zero.mp hh).resolve_left hl
    have hall : ∀ x ∈ Submodule.span ℂ (Set.range (fun β : Fin 3 → Fin m → ℕ =>
        homogToBlock n (gmon (frame a) β))), ⟪x, r⟫_ℂ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨β, rfl⟩ := hx; exact ho β
      | zero => simp
      | add x y hx hy ix iy => simp only [inner_add_left, ix, iy, add_zero]
      | smul z x hx ix => simp only [inner_smul_left, ix, mul_zero]
    have hz : r = 0 := inner_self_eq_zero.mp (hall r (block_gmon_span n a r))
    have he : v = S.starProjection v := sub_eq_zero.mp hz
    rw [he]
    exact S.starProjection_apply_mem v
  · exact hS

/-- The kernel projection is the rank-one sum over the orthonormal family. -/
lemma starProjection_MopB_eq_sum (n : ℕ) (a : Fin 3)
    (v : BlockSp (degB3 (m := m)) n) :
    (LinearMap.ker (toBlock3 (MopB (m := m) a) n)).starProjection v =
      ∑ j, ⟪eVecQ n a j, v⟫_ℂ • eVecQ n a j := by
  classical
  apply (LinearMap.ker (toBlock3 (MopB a) n)).eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (eVecQ_mem_ker n a j)
  · intro w hw
    rw [ker_MopB_eq_span] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      simp only [inner_sub_left, sum_inner, inner_smul_left, gram_eVecQ, ite_true]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [inner_conj_symm]
      simp
    | zero => simp
    | add x y hx hy ix iy => simp [inner_add_right, ix, iy]
    | smul z x hx ix => simp [inner_smul_right, ix]

/-- The averaged kernel projection of the three blocked difference-number
operators (the block of the three-copy test average). -/
noncomputable def Tq3 (m n : ℕ) :
    BlockSp (degB3 (m := m)) n →ₗ[ℂ] BlockSp (degB3 (m := m)) n :=
  (3 : ℂ)⁻¹ • (((LinearMap.ker (toBlock3 (MopB 0) n)).starProjection
      + (LinearMap.ker (toBlock3 (MopB 1) n)).starProjection
      + (LinearMap.ker (toBlock3 (MopB 2) n)).starProjection :
        BlockSp (degB3 (m := m)) n →L[ℂ] BlockSp (degB3 (m := m)) n) :
        BlockSp (degB3 (m := m)) n →ₗ[ℂ] BlockSp (degB3 (m := m)) n)

/-- The actual block of the three-copy average is the sum of its rotated
occupation-family rank-one operators. Orthogonality of distinct occupation
labels is recorded in `gram_eVecQ`. -/
theorem Tq3_eq_family_average (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    Tq3 m n v = (1 / 3 : ℂ) •
      ∑ j, ∑ a, ⟪eVecQ n a j, v⟫_ℂ • eVecQ n a j := by
  simp [Tq3, starProjection_MopB_eq_sum, Fin.sum_univ_three,
    Finset.sum_add_distrib, smul_add]

/-- Lemma 6.6's nonzero-spectrum correspondence for the actual rotated
occupation decomposition. The multiplicity labels are the centre-of-mass
occupations `p` and the in-plane occupations `q`; `k=|q|`. -/
theorem blockSpectrumQ_nonzero (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    z ∈ spectrum ℂ (Tq3 m n) ↔
      ∃ j : {i // degB2 (m := m) i = n},
        z = (coherentSectorConstantEigenvalue (degB j.val.2) : ℂ) ∨
        z = (coherentSectorSumZeroEigenvalue (degB j.val.2) : ℂ) := by
  simpa only [coherentSectorConstantEigenvalue, coherentSectorSumZeroEigenvalue, sQ] using
    three_family_average_mem_spectrum_iff (eVecQ n) sQ (gram_eVecQ n)
      (Tq3 m n) (Tq3_eq_family_average n) z hz

/-- **Lemma 6.6, per-block form**: the averaged kernel projection `T` of the
three difference-number operators satisfies `(T - I)(T - (1/2)I) ≥ 0`. -/
theorem blockGapQ (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    0 ≤ (⟪v, ((Tq3 m n - LinearMap.id) ∘ₗ
        (Tq3 m n - (((1 / 2 : ℝ) : ℂ) • LinearMap.id))) v⟫_ℂ).re := by
  classical
  exact three_projection_gap_of_gram (eVecQ n) sQ (gram_eVecQ n) sQ_mem
    (fun a => (LinearMap.ker (toBlock3 (MopB a) n)).starProjection.toLinearMap)
    (starProjection_MopB_eq_sum n) (Tq3 m n) rfl v

end GaussianTesting
