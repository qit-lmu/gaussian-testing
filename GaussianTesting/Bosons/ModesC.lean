module

/-
Copyright (c) 2026 Jop Briët, Castro-Silva, Walter, Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Main
public import GaussianTesting.Bosons.Modes

@[expose] public section

/-!
# Complex two-copy modes, the kernel of `Λ`, and the swap–parity operator

Complex-coefficient combination modes on the two-copy coefficient space
`FA2 m`, mirroring `Bosons/Modes.lean` (which is rational, three-copy) with a
Hermitian pairing. The kernel of `lambdaB` is spanned on each degree block by
balanced monomials. The swap–parity operator `W` (swap the copies and apply
parity to one copy) fixes this kernel pointwise. Lemma 6.2 uses this property.

## Ladder structure

`[lambdaB, AdmC c l] = AdmC (rotC c) l` with `rotC (c₀, c₁) = (−i·c₁, i·c₀)`.
Eigenmodes: `cPlus = (1, i)` (eigenvalue `+1`), `cMinus = (1, −i)` (`−1`);
they are `pairH`-orthogonal with `pairH c± c± = 2`.  Monomials in these modes
diagonalise `lambdaB` with eigenvalue `|α| − |β|`, so the kernel of each block
is the span of the *balanced* monomials.  `W` acts on monomials by
`(−i)^{|α|} i^{|β|}`, hence is the identity on the kernel.
-/

namespace GaussianTesting

open Complex Finsupp Finset
open scoped InnerProductSpace ComplexConjugate ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false

variable {m : ℕ}

local notation "⟪" x ", " y "⟫_ℂ" => inner ℂ x y

/-! ### Complex combination modes and the Hermitian pairing -/

/-- Annihilation operator of the complex combination mode `c` (antilinear in
`c`, so that the CCR produces the Hermitian pairing). -/
noncomputable def AmC (c : Fin 2 → ℂ) (l : Fin m) : FA2 m →ₗ[ℂ] FA2 m :=
  (starRingEnd ℂ (c 0)) • copyL (aF l) + (starRingEnd ℂ (c 1)) • copyR (aF l)

/-- Creation operator of the complex combination mode `c`. -/
noncomputable def AdmC (c : Fin 2 → ℂ) (l : Fin m) : FA2 m →ₗ[ℂ] FA2 m :=
  c 0 • copyL (adF l) + c 1 • copyR (adF l)

/-- Hermitian pairing of complex mode vectors. -/
def pairH (c c' : Fin 2 → ℂ) : ℂ := ∑ t, starRingEnd ℂ (c t) * c' t

private lemma basis_ext {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    {S T : (ι →₀ ℂ) →ₗ[ℂ] V}
    (h : ∀ p, S (Finsupp.single p 1) = T (Finsupp.single p 1)) : S = T := by
  apply Finsupp.lhom_ext
  intro p c
  have he : Finsupp.single p c = c • Finsupp.single p 1 := by simp
  rw [he, map_smul, map_smul, h]

private lemma copyL_single (A : FA m →ₗ[ℂ] FA m)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    copyL A (Finsupp.single p z) = z •
      Finsupp.lmapDomain ℂ ℂ (fun i => (i, p.2))
        (A (Finsupp.single p.1 1)) := by
  simp [copyL, Finsupp.lsum_single]

private lemma copyL_slice (A : FA m →ₗ[ℂ] FA m) (b : Fin m → ℕ) (v : FA m) :
    copyL A (Finsupp.lmapDomain ℂ ℂ (fun i => (i, b)) v) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (i, b)) (A v) := by
  have he : copyL A ∘ₗ Finsupp.lmapDomain ℂ ℂ (fun i => (i, b)) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (i, b)) ∘ₗ A := by
    apply basis_ext
    intro p
    simp [copyL_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun he v

private lemma copyL_comp (A B : FA m →ₗ[ℂ] FA m) :
    copyL A ∘ₗ copyL B = copyL (A ∘ₗ B) := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copyL_single, one_smul]
  exact copyL_slice A _ _

private lemma copyL_sub (A B : FA m →ₗ[ℂ] FA m) :
    copyL (A - B) = copyL A - copyL B := by
  apply basis_ext
  intro p
  simp only [copyL_single, LinearMap.sub_apply, map_sub, one_smul]

private lemma copyL_id : copyL (LinearMap.id : FA m →ₗ[ℂ] FA m) = LinearMap.id := by
  apply basis_ext
  intro p
  simp [copyL_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private lemma copyR_single (A : FA m →ₗ[ℂ] FA m)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    copyR A (Finsupp.single p z) = z •
      Finsupp.lmapDomain ℂ ℂ (fun i => (p.1, i))
        (A (Finsupp.single p.2 1)) := by
  simp [copyR, Finsupp.lsum_single]

private lemma copyR_slice (A : FA m →ₗ[ℂ] FA m) (b : Fin m → ℕ) (v : FA m) :
    copyR A (Finsupp.lmapDomain ℂ ℂ (fun i => (b, i)) v) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (b, i)) (A v) := by
  have he : copyR A ∘ₗ Finsupp.lmapDomain ℂ ℂ (fun i => (b, i)) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (b, i)) ∘ₗ A := by
    apply basis_ext
    intro p
    simp [copyR_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun he v

private lemma copyR_comp (A B : FA m →ₗ[ℂ] FA m) :
    copyR A ∘ₗ copyR B = copyR (A ∘ₗ B) := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copyR_single, one_smul]
  exact copyR_slice A _ _

private lemma copyR_sub (A B : FA m →ₗ[ℂ] FA m) :
    copyR (A - B) = copyR A - copyR B := by
  apply basis_ext
  intro p
  simp only [copyR_single, LinearMap.sub_apply, map_sub, one_smul]

private lemma copyR_id : copyR (LinearMap.id : FA m →ₗ[ℂ] FA m) = LinearMap.id := by
  apply basis_ext
  intro p
  simp [copyR_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private lemma copyL2_comm (A B : FA m →ₗ[ℂ] FA m) :
    copyL A ∘ₗ copyR B = copyR B ∘ₗ copyL A := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copyL_single, copyR_single, one_smul]
  simp only [copyL, copyR, Finsupp.lsum_apply, Finsupp.lmapDomain_apply]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
    Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
  simp only [LinearMap.toSpanSingleton_apply]
  unfold Finsupp.mapDomain Finsupp.sum
  simp only [Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

private lemma mode_ccr1 (l k : Fin m) :
    copyL (aF l) ∘ₗ copyL (adF k) - copyL (adF k) ∘ₗ copyL (aF l) =
      (if l = k then (1 : ℂ) else 0) • LinearMap.id := by
  classical
  rw [copyL_comp, copyL_comp, ← copyL_sub]
  by_cases h : l = k
  · subst k
    simp [ccr_same, copyL_id]
  · rw [(ccr_ne h).1]
    have hz : adF k ∘ₗ aF l - adF k ∘ₗ aF l = 0 := by
      ext v q
      simp
    rw [hz]
    simp only [h, ite_false, zero_smul]
    apply Finsupp.lhom_ext
    intro p z
    simp [copyL, Finsupp.lsum_single]

private lemma mode_ccr2 (l k : Fin m) :
    copyR (aF l) ∘ₗ copyR (adF k) - copyR (adF k) ∘ₗ copyR (aF l) =
      (if l = k then (1 : ℂ) else 0) • LinearMap.id := by
  classical
  rw [copyR_comp, copyR_comp, ← copyR_sub]
  by_cases h : l = k
  · subst k
    simp [ccr_same, copyR_id]
  · rw [(ccr_ne h).1]
    have hz : adF k ∘ₗ aF l - adF k ∘ₗ aF l = 0 := by
      ext v q
      simp
    rw [hz]
    simp only [h, ite_false, zero_smul]
    apply Finsupp.lhom_ext
    intro p z
    simp [copyR, Finsupp.lsum_single]


/-- CCR: `[AmC c l, AdmC c' l'] = δ_{l l'} ⟨c, c'⟩`. -/
theorem ccrC (c c' : Fin 2 → ℂ) (l l' : Fin m) :
    AmC c l ∘ₗ AdmC c' l' - AdmC c' l' ∘ₗ AmC c l
      = (if l = l' then pairH c c' else 0) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  have h1 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) (mode_ccr1 l l')
  have h2 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) (mode_ccr2 l l')
  have h12 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) (copyL2_comm (aF l) (adF l'))
  have h21 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) ((copyL2_comm (adF l') (aF l)).symm)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at *
  simp only [AmC, AdmC, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, pairH, Fin.sum_univ_two]
  split_ifs at * <;>
    linear_combination
      (starRingEnd ℂ (c 0)) * c' 0 * h1 +
      (starRingEnd ℂ (c 1)) * c' 1 * h2 +
      (starRingEnd ℂ (c 0)) * c' 1 * h12 +
      (starRingEnd ℂ (c 1)) * c' 0 * h21

theorem admC_admC_comm (c c' : Fin 2 → ℂ) (l l' : Fin m) :
    AdmC c l ∘ₗ AdmC c' l' = AdmC c' l' ∘ₗ AdmC c l := by
  classical
  have hc : adF l ∘ₗ adF l' = adF l' ∘ₗ adF l := by
    by_cases h : l = l'
    · subst l'; rfl
    · exact (ccr_ne h).2.2
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  have h1 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) (show copyL (adF l) ∘ₗ copyL (adF l') = copyL (adF l') ∘ₗ copyL (adF l) by rw [copyL_comp, copyL_comp, hc])
  have h2 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) (show copyR (adF l) ∘ₗ copyR (adF l') = copyR (adF l') ∘ₗ copyR (adF l) by rw [copyR_comp, copyR_comp, hc])
  have h12 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) (copyL2_comm (adF l) (adF l'))
  have h21 := congrArg (fun T : FA2 m →ₗ[ℂ] FA2 m => T v q) ((copyL2_comm (adF l') (adF l)).symm)
  simp only [LinearMap.comp_apply] at *
  simp only [AdmC, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  linear_combination
      c 0 * c' 0 * h1 + c 1 * c' 1 * h2 +
      c 0 * c' 1 * h12 + c 1 * c' 0 * h21

/-- The two-copy vacuum. -/
noncomputable def vac2 : FA2 m := Finsupp.single ((fun _ => 0), (fun _ => 0)) 1

theorem AmC_vac2 (c : Fin 2 → ℂ) (l : Fin m) : AmC c l (vac2 (m := m)) = 0 := by
  classical
  simp [AmC, vac2, copyL, copyR, aF, Finsupp.lsum_single]

/-! ### Words and exponent monomials (complex mirror of `Bosons/Modes.lean`) -/

/-- Monomial of a creation word. -/
noncomputable def monWC (L : List ((Fin 2 → ℂ) × Fin m)) : FA2 m :=
  ((L.map fun x => AdmC x.1 x.2).prod : FA2 m →ₗ[ℂ] FA2 m) vac2

theorem monWC_cons (x : (Fin 2 → ℂ) × Fin m) (L : List ((Fin 2 → ℂ) × Fin m)) :
    monWC (x :: L) = AdmC x.1 x.2 (monWC L) := by
  simp [monWC, Module.End.mul_apply]

theorem monWC_perm {L L' : List ((Fin 2 → ℂ) × Fin m)} (h : L.Perm L') :
    monWC L = monWC L' := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [monWC_cons, ih]
  | swap x y L =>
    simp only [monWC_cons]
    change (AdmC y.1 y.2 ∘ₗ AdmC x.1 x.2) (monWC L) =
      (AdmC x.1 x.2 ∘ₗ AdmC y.1 y.2) (monWC L)
    exact LinearMap.congr_fun (admC_admC_comm y.1 x.1 y.2 x.2) (monWC L)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem AmC_monWC_cons (c : Fin 2 → ℂ) (l : Fin m) (x : (Fin 2 → ℂ) × Fin m)
    (L : List ((Fin 2 → ℂ) × Fin m)) :
    AmC c l (monWC (x :: L)) =
      (if l = x.2 then pairH c x.1 else 0) • monWC L
        + AdmC x.1 x.2 (AmC c l (monWC L)) := by
  have h := LinearMap.congr_fun (ccrC c x.1 l x.2) (monWC L)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h
  rw [monWC_cons]
  exact eq_add_of_sub_eq h


section GmonC

variable {κ : Type*} [fintypeκ : Fintype κ] [decidableEqκ : DecidableEq κ]

/-- Canonical word of a slot family with exponents. -/
noncomputable def expWordC (X : κ → Fin 2 → ℂ) (α : κ → Fin m → ℕ) :
    List ((Fin 2 → ℂ) × Fin m) :=
  (Finset.univ : Finset κ).toList.flatMap fun s =>
    (List.finRange m).flatMap fun l => List.replicate (α s l) (X s, l)

/-- Exponent-indexed monomial. -/
noncomputable def gmonC (X : κ → Fin 2 → ℂ) (α : κ → Fin m → ℕ) : FA2 m :=
  monWC (expWordC X α)

omit fintypeκ decidableEqκ in
@[simp] theorem gmonC_zero [Fintype κ] [DecidableEq κ] (X : κ → Fin 2 → ℂ) :
    gmonC (m := m) X 0 = vac2 := by
  have h : expWordC (m := m) X 0 = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro s hs
    apply List.flatMap_eq_nil_iff.mpr
    intro l hl
    simp
  simp [gmonC, h, monWC]

private lemma flatMap_bump_perm {ι A : Type*} [DecidableEq ι]
    (L : List ι) (hn : L.Nodup) (t : ι) (ht : t ∈ L)
    (f g : ι → List A) (a : A)
    (he : ∀ i ∈ L, i ≠ t → g i = f i)
    (hb : (g t).Perm (a :: f t)) :
    (L.flatMap g).Perm (a :: L.flatMap f) := by
  induction L with
  | nil => simp at ht
  | cons i L ih =>
    obtain ⟨hin, hn⟩ := List.nodup_cons.mp hn
    by_cases hit : i = t
    · subst i
      have htail : L.flatMap g = L.flatMap f := by
        apply List.flatMap_congr
        intro i hi
        exact he i (by simp [hi]) (by intro h; subst i; exact hin hi)
      simpa [List.flatMap_cons, htail] using hb.append_right (L.flatMap f)
    · have ht' : t ∈ L := by simpa [hit, Ne.symm hit] using ht
      have hh := ih hn ht' (fun j hj hjt => he j (by simp [hj]) hjt)
      simp only [List.flatMap_cons, he i (by simp) hit]
      exact (hh.append_left (f i)).trans List.perm_middle

private lemma expWordC_bump_perm (X : κ → Fin 2 → ℂ)
    (α : κ → Fin m → ℕ) (s : κ) (l : Fin m) :
    (expWordC X (bump α s l)).Perm ((X s, l) :: expWordC X α) := by
  unfold expWordC
  apply flatMap_bump_perm _ (Finset.nodup_toList _) s (by simp)
  · intro t ht hts
    simp [bump, Function.update_of_ne hts]
  · apply flatMap_bump_perm _ (List.nodup_finRange _) l (by simp)
    · intro k hk hkl
      simp [bump, Function.update_of_ne hkl]
    · simp [bump, List.replicate_succ]


theorem gmonC_succ (X : κ → Fin 2 → ℂ) (α : κ → Fin m → ℕ) (s₀ : κ) (l : Fin m) :
    AdmC (X s₀) l (gmonC X α) = gmonC X (bump α s₀ l) := by
  exact (monWC_cons (X s₀, l) (expWordC X α)).symm.trans
    (monWC_perm (expWordC_bump_perm X α s₀ l)).symm

omit fintypeκ decidableEqκ in
private lemma bump_apply [Fintype κ] [DecidableEq κ] (α : κ → Fin m → ℕ) (s t : κ) (l k : Fin m) :
    bump α s l t k = α t k + if t = s ∧ k = l then 1 else 0 := by
  by_cases ht : t = s <;> by_cases hk : k = l <;> simp_all [bump]

omit fintypeκ decidableEqκ in
private lemma bump_debump [Fintype κ] [DecidableEq κ] (α : κ → Fin m → ℕ) (s : κ) (l : Fin m)
    (h : α s l ≠ 0) : bump (debump α s l) s l = α := by
  ext t k
  by_cases ht : t = s <;> by_cases hk : k = l <;>
    simp_all [bump, debump, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]

omit fintypeκ decidableEqκ in
private lemma debump_bump [Fintype κ] [DecidableEq κ] (α : κ → Fin m → ℕ) (s : κ) (l : Fin m) :
    debump (bump α s l) s l = α := by
  ext t k
  by_cases ht : t = s <;> by_cases hk : k = l <;> simp_all [bump, debump]

omit fintypeκ decidableEqκ in
private lemma debump_bump_ne [Fintype κ] [DecidableEq κ] (α : κ → Fin m → ℕ) (s t : κ) (l k : Fin m)
    (h : s ≠ t ∨ l ≠ k) :
    debump (bump α t k) s l = bump (debump α s l) t k := by
  ext u j
  by_cases hus : u = s <;> by_cases hut : u = t <;>
    by_cases hjl : j = l <;> by_cases hjk : j = k <;>
      simp_all [bump, debump]

private lemma exp_total_bump (α : κ → Fin m → ℕ) (s : κ) (l : Fin m) :
    (∑ t, ∑ k, bump α s l t k) = (∑ t, ∑ k, α t k) + 1 := by
  simp only [bump_apply, ite_and, Finset.sum_add_distrib]
  simp [Finset.sum_ite_irrel]

private lemma exp_induction (P : (κ → Fin m → ℕ) → Prop)
    (hzero : P 0) (hstep : ∀ α s l, P α → P (bump α s l)) (α : κ → Fin m → ℕ) :
    P α := by
  suffices h : ∀ n, ∀ α : κ → Fin m → ℕ, (∑ s, ∑ l, α s l) = n → P α from
    h _ α rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α hn
    by_cases hz : α = 0
    · simpa [hz] using hzero
    · obtain ⟨s, hs⟩ := Function.ne_iff.mp hz
      obtain ⟨l, hl⟩ := Function.ne_iff.mp hs
      have hl' : α s l ≠ 0 := hl
      have hb := bump_debump α s l hl'
      have hd := exp_total_bump (debump α s l) s l
      rw [hb, hn] at hd
      rw [← hb]
      exact hstep _ s l (ih _ (by omega) _ rfl)

private lemma exp_orth_bump {c : Fin 2 → ℂ} {X : κ → Fin 2 → ℂ}
    {α : κ → Fin m → ℕ} {s t : κ} {k : Fin m}
    (h : ∀ u, u ≠ s → bump α t k u ≠ 0 → pairH c (X u) = 0) :
    ∀ u, u ≠ s → α u ≠ 0 → pairH c (X u) = 0 := by
  intro u hus hu
  apply h u hus
  intro hz
  apply hu
  ext j
  have hj := congrFun hz j
  rw [bump_apply] at hj
  simp only [Pi.zero_apply] at hj ⊢
  omega

private lemma AmC_gmonC_cross (c : Fin 2 → ℂ) (X : κ → Fin 2 → ℂ)
    (α : κ → Fin m → ℕ) (s : κ) (l : Fin m)
    (horth : ∀ t, t ≠ s → α t ≠ 0 → pairH c (X t) = 0) :
    AmC c l (gmonC X α) =
      ((α s l : ℂ) * pairH c (X s)) • gmonC X (debump α s l) := by
  induction α using exp_induction with
  | hzero =>
    simp [gmonC_zero, AmC_vac2]
  | hstep α t k ih =>
    have ho := exp_orth_bump horth
    have ladder : AmC c l (gmonC X (bump α t k)) =
        (if l = k then pairH c (X t) else 0) • gmonC X α +
          AdmC (X t) k (AmC c l (gmonC X α)) := by
      rw [← gmonC_succ]
      exact AmC_monWC_cons c l (X t, k) (expWordC X α)
    rw [ladder, ih ho, map_smul, gmonC_succ]
    by_cases ht : t = s
    · subst t
      by_cases hk : k = l
      · subst k
        rw [debump_bump, bump_apply]
        simp only [and_self, ite_true, Nat.cast_add, Nat.cast_one]
        by_cases hz : α s l = 0
        · simp [hz]
        · rw [bump_debump α s l hz]
          module
      · rw [debump_bump_ne α s s l k (Or.inr (Ne.symm hk)), bump_apply]
        simp [Ne.symm hk]
    · have hpair : pairH c (X t) = 0 := by
        apply horth t ht
        intro hz
        have hh := congrFun hz k
        simp [bump] at hh
      rw [debump_bump_ne α s t l k (Or.inl (Ne.symm ht)), bump_apply]
      simp [Ne.symm ht, hpair]


theorem AmC_gmonC (X : κ → Fin 2 → ℂ) (α : κ → Fin m → ℕ) (s₀ : κ)
    (horth : ∀ t, t ≠ s₀ → α t ≠ 0 → pairH (X s₀) (X t) = 0) (l : Fin m) :
    AmC (X s₀) l (gmonC X α) =
      ((α s₀ l : ℂ) * pairH (X s₀) (X s₀)) • gmonC X (debump α s₀ l) := by
  exact AmC_gmonC_cross (X s₀) X α s₀ l horth

end GmonC

/-! ### The pairing and the Gram formula -/

/-- The standard sesquilinear pairing on `FA2 m`. -/
def pairF2 (f g : FA2 m) : ℂ := f.sum fun i z => (starRingEnd ℂ) z * g i

private theorem pairF2_add_left (f f' g : FA2 m) :
    pairF2 (f + f') g = pairF2 f g + pairF2 f' g := by
  classical
  unfold pairF2
  exact Finsupp.sum_add_index (by simp) (by intros; simp [add_mul])

private theorem pairF2_add_right (f g g' : FA2 m) :
    pairF2 f (g + g') = pairF2 f g + pairF2 f g' := by
  classical
  simp [pairF2, Finsupp.sum, mul_add, Finset.sum_add_distrib]

private theorem pairF2_smul_left (z : ℂ) (f g : FA2 m) :
    pairF2 (z • f) g = (starRingEnd ℂ) z * pairF2 f g := by
  classical
  unfold pairF2
  rw [Finsupp.sum_smul_index' (by simp)]
  simp [Finsupp.sum, map_mul, mul_assoc, Finset.mul_sum]

private theorem pairF2_smul_right (z : ℂ) (f g : FA2 m) :
    pairF2 f (z • g) = z * pairF2 f g := by
  classical
  simp [pairF2, Finsupp.sum, Finset.mul_sum, mul_left_comm]

@[simp] private theorem pairF2_zero_left (g : FA2 m) : pairF2 0 g = 0 := by
  simp [pairF2]

@[simp] private theorem pairF2_zero_right (f : FA2 m) : pairF2 f 0 = 0 := by
  simp [pairF2]

@[simp] private theorem pairF2_vac2_vac2 : pairF2 (vac2 (m := m)) vac2 = 1 := by
  classical
  simp [pairF2, vac2]

private lemma pairF2_single_left (p : (Fin m → ℕ) × (Fin m → ℕ))
    (z : ℂ) (g : FA2 m) : pairF2 (Finsupp.single p z) g = star z * g p := by
  classical
  simp [pairF2, Finsupp.sum_single_index]

private lemma pairF2_single_right (f : FA2 m)
    (q : (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    pairF2 f (Finsupp.single q z) = star (f q) * z := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp [pairF2_add_left, hf, hg, add_mul]
  | single p w =>
    simp [pairF2_single_left, Finsupp.single_apply, eq_comm]
    split_ifs <;> simp_all

private lemma pairF2_adj (A B : FA2 m →ₗ[ℂ] FA2 m)
    (h : ∀ p q, (A (Finsupp.single p 1)) q =
      star ((B (Finsupp.single q 1)) p)) (f g : FA2 m) :
    pairF2 (A f) g = pairF2 f (B g) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [map_add, pairF2_add_left, hf, hf']
  | single p z =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp [map_add, pairF2_add_right, hg, hg']
    | single q w =>
      have hz : Finsupp.single p z = z • Finsupp.single p 1 := by simp
      have hw : Finsupp.single q w = w • Finsupp.single q 1 := by simp
      rw [pairF2_single_right, hw, map_smul, hz, map_smul,
        pairF2_smul_left, pairF2_single_left]
      simp [h, mul_comm, mul_left_comm]


private lemma entry_L_aF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (copyL (aF l) (Finsupp.single p 1)) q =
      ((aF l (Finsupp.single p.1 1)) q.1) *
      ((Finsupp.single p.2 (1 : ℂ)) q.2) := by
  classical
  rcases p with ⟨p1,p2⟩
  rcases q with ⟨q1,q2⟩
  simp [copyL, aF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma entry_L_adF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (copyL (adF l) (Finsupp.single p 1)) q =
      ((adF l (Finsupp.single p.1 1)) q.1) *
      ((Finsupp.single p.2 (1 : ℂ)) q.2) := by
  classical
  rcases p with ⟨p1,p2⟩
  rcases q with ⟨q1,q2⟩
  simp [copyL, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma pairF2_copyL_adm (l : Fin m) (f g : FA2 m) :
    pairF2 (copyL (adF l) f) g = pairF2 f (copyL (aF l) g) := by
  apply pairF2_adj
  intro p q
  rw [entry_L_adF, entry_L_aF, adF_entry]
  have h : (Finsupp.single p.2 (1 : ℂ)) q.2 =
      star ((Finsupp.single q.2 (1 : ℂ)) p.2) := by
    classical
    simp [Finsupp.single_apply, eq_comm]
  rw [h, star_mul]
  ring

private lemma entry_R_aF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (copyR (aF l) (Finsupp.single p 1)) q =
      ((aF l (Finsupp.single p.2 1)) q.2) *
      ((Finsupp.single p.1 (1 : ℂ)) q.1) := by
  classical
  rcases p with ⟨p1,p2⟩
  rcases q with ⟨q1,q2⟩
  simp [copyR, aF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma entry_R_adF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ)) :
    (copyR (adF l) (Finsupp.single p 1)) q =
      ((adF l (Finsupp.single p.2 1)) q.2) *
      ((Finsupp.single p.1 (1 : ℂ)) q.1) := by
  classical
  rcases p with ⟨p1,p2⟩
  rcases q with ⟨q1,q2⟩
  simp [copyR, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma pairF2_copyR_adm (l : Fin m) (f g : FA2 m) :
    pairF2 (copyR (adF l) f) g = pairF2 f (copyR (aF l) g) := by
  apply pairF2_adj
  intro p q
  rw [entry_R_adF, entry_R_aF, adF_entry]
  have h : (Finsupp.single p.1 (1 : ℂ)) q.1 =
      star ((Finsupp.single q.1 (1 : ℂ)) p.1) := by
    classical
    simp [Finsupp.single_apply, eq_comm]
  rw [h, star_mul]
  ring

theorem pairF2_admC (c : Fin 2 → ℂ) (l : Fin m) (f g : FA2 m) :
    pairF2 (AdmC c l f) g = pairF2 f (AmC c l g) := by
  simp [AdmC, AmC, pairF2_add_left, pairF2_add_right, pairF2_smul_left,
    pairF2_smul_right, pairF2_copyL_adm, pairF2_copyR_adm]

section GramC

variable {κ : Type*} [fintypeκ : Fintype κ] [decidableEqκ : DecidableEq κ]

private lemma pairF2_symm (f g : FA2 m) : pairF2 f g = star (pairF2 g f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [pairF2_add_left, pairF2_add_right, hf, hf']
  | single p z =>
    rw [pairF2_single_left, pairF2_single_right]
    simp [star_mul, mul_comm]

private lemma pairF2_vac_adm (c : Fin 2 → ℂ) (l : Fin m) (f : FA2 m) :
    pairF2 vac2 (AdmC c l f) = 0 := by
  rw [pairF2_symm, pairF2_admC, AmC_vac2, pairF2_zero_right, star_zero]

omit fintypeκ decidableEqκ in
private lemma bump_not_zero [Fintype κ] [DecidableEq κ] (α : κ → Fin m → ℕ) (s : κ) (l : Fin m) :
    bump α s l ≠ 0 := by
  intro hz
  have h := congrFun (congrFun hz s) l
  simp [bump] at h

private lemma exp_le_bump (α : κ → Fin m → ℕ) (s t : κ) (l k : Fin m) :
    α t k ≤ bump α s l t k := by rw [bump_apply]; omega

omit fintypeκ decidableEqκ in
private lemma debump_le [Fintype κ] [DecidableEq κ] (α : κ → Fin m → ℕ) (s t : κ) (l k : Fin m) :
    debump α s l t k ≤ α t k := by
  by_cases ht : t = s <;> by_cases hk : k = l <;> simp_all [debump]

private lemma pairF2_vac_gmonC (Y : κ → Fin 2 → ℂ) (β : κ → Fin m → ℕ) :
    pairF2 vac2 (gmonC Y β) = if β = 0 then 1 else 0 := by
  induction β using exp_induction with
  | hzero => simp
  | hstep β s l ih =>
    rw [← gmonC_succ, pairF2_vac_adm]
    simp [bump_not_zero]

private lemma gram_product_bump (X Y : κ → Fin 2 → ℂ)
    (α : κ → Fin m → ℕ) (s : κ) (l : Fin m) :
    (∏ t, ∏ k, ((bump α s l t k).factorial : ℂ) *
      pairH (X t) (Y t) ^ (bump α s l t k)) =
    ((α s l + 1 : ℕ) : ℂ) * pairH (X s) (Y s) *
      (∏ t, ∏ k, ((α t k).factorial : ℂ) * pairH (X t) (Y t) ^ (α t k)) := by
  classical
  let F := fun (t : κ) (k : Fin m) (n : ℕ) =>
    (n.factorial : ℂ) * pairH (X t) (Y t) ^ n
  change (∏ t, ∏ k, F t k (bump α s l t k)) =
    ((α s l + 1 : ℕ) : ℂ) * pairH (X s) (Y s) * (∏ t, ∏ k, F t k (α t k))
  rw [← Finset.mul_prod_erase Finset.univ (fun t => ∏ k, F t k (bump α s l t k)) (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun t => ∏ k, F t k (α t k)) (Finset.mem_univ s)]
  have he : (∏ t ∈ Finset.univ.erase s, ∏ k, F t k (bump α s l t k)) =
      ∏ t ∈ Finset.univ.erase s, ∏ k, F t k (α t k) := by
    apply Finset.prod_congr rfl
    intro t ht
    simp [bump, Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  rw [he]
  have hi : (∏ k, F s k (bump α s l s k)) =
      ((α s l + 1 : ℕ) : ℂ) * pairH (X s) (Y s) * ∏ k, F s k (α s k) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => F s k (bump α s l s k)) (Finset.mem_univ l),
      ← Finset.mul_prod_erase Finset.univ (fun k => F s k (α s k)) (Finset.mem_univ l)]
    have he' : (∏ k ∈ Finset.univ.erase l, F s k (bump α s l s k)) =
        ∏ k ∈ Finset.univ.erase l, F s k (α s k) := by
      apply Finset.prod_congr rfl
      intro k hk
      simp [bump, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    rw [he']
    simp only [bump, Function.update_self, F, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  rw [hi]
  ring


/-- Gram/Wick formula for complex-mode monomials with diagonal used cross
pairings. -/
theorem gram_diagC (X Y : κ → Fin 2 → ℂ) (α β : κ → Fin m → ℕ)
    (hdiag : ∀ s t : κ, s ≠ t → α s ≠ 0 → β t ≠ 0 → pairH (X s) (Y t) = 0) :
    pairF2 (gmonC (m := m) X α) (gmonC Y β) =
      if α = β then
        (∏ s, ∏ l, ((α s l).factorial : ℂ) * pairH (X s) (Y s) ^ (α s l))
      else 0 := by
  classical
  induction α using exp_induction generalizing β with
  | hzero =>
    rw [gmonC_zero, pairF2_vac_gmonC]
    by_cases hβ : β = 0
    · subst β
      simp
    · simp [hβ, Ne.symm hβ]
  | hstep α s l ih =>
    have hused : bump α s l s ≠ 0 := by
      intro hz
      have hh := congrFun hz l
      simp [bump] at hh
    have horth : ∀ t, t ≠ s → β t ≠ 0 → pairH (X s) (Y t) = 0 := by
      intro t hts ht
      exact hdiag s t (Ne.symm hts) hused ht
    have hdiag' : ∀ u t, u ≠ t → α u ≠ 0 →
        debump β s l t ≠ 0 → pairH (X u) (Y t) = 0 := by
      intro u t hut hu ht
      apply hdiag u t hut
      · intro hz
        apply hu
        ext k
        have hk := congrFun hz k
        have hh := exp_le_bump α s u l k
        simp only [Pi.zero_apply] at hk ⊢
        omega
      · intro hz
        apply ht
        ext k
        have hh := debump_le β s t l k
        simp only [hz, Pi.zero_apply] at hh ⊢
        omega
    rw [← gmonC_succ, pairF2_admC, AmC_gmonC_cross (X s) Y β s l horth,
      pairF2_smul_right, ih _ hdiag']
    by_cases hz : β s l = 0
    · have hne : bump α s l ≠ β := by
        intro he
        have hh := congrFun (congrFun he s) l
        simp [bump, hz] at hh
      simp [hz, hne]
    · have hb := bump_debump β s l hz
      by_cases he : α = debump β s l
      · have hβ : β = bump α s l := by rw [he]; exact hb.symm
        subst β
        simp only [debump_bump, ite_true]
        rw [show bump α s l s l = α s l + 1 by simp [bump]]
        exact (gram_product_bump X Y α s l).symm
      · have hne : bump α s l ≠ β := by
          intro hh
          apply he
          rw [← hh, debump_bump]
        simp [he, hne]

end GramC

/-! ### Homogeneity and completeness -/

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

private lemma degB_bump {κ : Type*} [Fintype κ] [DecidableEq κ]
    (α : κ → Fin m → ℕ) (s t : κ) (l : Fin m) :
    degB (bump α s l t) = degB (α t) + if t = s then 1 else 0 := by
  classical
  by_cases h : t = s
  · subst t
    simp only [bump, Function.update_self, ite_true]
    have hd := degB_update (α s) l (α s l + 1)
    omega
  · simp [bump, h]

private lemma support_image_degree (T : FA2 m →ₗ[ℂ] FA2 m) (a b : ℕ)
    (hT : ∀ p q, q ∈ (T (Finsupp.single p 1)).support →
      degB2 q + a = degB2 p + b)
    (f : FA2 m) (q : (Fin m → ℕ) × (Fin m → ℕ))
    (hq : q ∈ (T f).support) :
    ∃ p ∈ f.support, degB2 q + a = degB2 p + b := by
  classical
  by_contra hn
  have hf : (∑ p ∈ f.support, f p • Finsupp.single p 1) = f := by
    simpa [Finsupp.sum] using f.sum_single
  have hz : (T f) q = 0 := by
    rw [← hf]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have he : (T (Finsupp.single p 1)) q = 0 := by
      by_contra he
      exact hn ⟨p, hp, hT p q (Finsupp.mem_support_iff.mpr he)⟩
    simp [he]
  exact Finsupp.mem_support_iff.mp hq hz

private lemma shift_1_adF (l : Fin m) :
    ∀ p q, q ∈ (copyL (adF l) (Finsupp.single p 1)).support →
      degB2 q = degB2 p + 1 := by
  classical
  intro p q h
  simp only [copyL, adF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hd := degB_update p.1 l (p.1 l + 1)
  dsimp [degB2]
  omega

private lemma shift_2_adF (l : Fin m) :
    ∀ p q, q ∈ (copyR (adF l) (Finsupp.single p 1)).support →
      degB2 q = degB2 p + 1 := by
  classical
  intro p q h
  simp only [copyR, adF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hd := degB_update p.2 l (p.2 l + 1)
  dsimp [degB2]
  omega


private lemma shift_AdmC (c : Fin 2 → ℂ) (l : Fin m) :
    ∀ p q, q ∈ (AdmC c l (Finsupp.single p 1)).support →
      degB2 q = degB2 p + 1 := by
  intro p q h
  simp only [AdmC, LinearMap.add_apply, LinearMap.smul_apply] at h
  rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
  · exact shift_1_adF l p q (Finsupp.support_smul h)
  · exact shift_2_adF l p q (Finsupp.support_smul h)

/-- `degB2`-homogeneity. -/
def IsHomog2 (n : ℕ) (f : FA2 m) : Prop := ∀ i ∈ f.support, degB2 i = n

private theorem isHomog2_adm {n : ℕ} {f : FA2 m} (hf : IsHomog2 n f)
    (c : Fin 2 → ℂ) (l : Fin m) : IsHomog2 (n + 1) (AdmC c l f) := by
  intro q hq
  obtain ⟨p, hp, hd⟩ := support_image_degree (AdmC c l) 0 1
    (by simpa using shift_AdmC c l) f q hq
  simpa [hf p hp] using hd


theorem gmonC_homog {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : κ → Fin 2 → ℂ) (α : κ → Fin m → ℕ) :
    IsHomog2 (∑ s, degB (α s)) (gmonC (m := m) X α) := by
  induction α using exp_induction with
  | hzero =>
    simp only [gmonC_zero]
    intro i hi
    obtain ⟨he, hc⟩ := (Finsupp.mem_support_single _ _ _).mp hi
    subst i
    simp [degB2, degB]
  | hstep α s l ih =>
    rw [← gmonC_succ]
    simpa only [degB, exp_total_bump] using isHomog2_adm ih (X s) l

private lemma AdmC_vec_add (c d : Fin 2 → ℂ) (l : Fin m) :
    AdmC (c + d) l = AdmC c l + AdmC d l := by
  simp only [AdmC, Pi.add_apply, add_smul]
  module
private lemma AdmC_vec_smul (z : ℂ) (c : Fin 2 → ℂ) (l : Fin m) :
    AdmC (z • c) l = z • AdmC c l := by
  simp only [AdmC, Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]
private lemma gmonC_span_stable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : κ → Fin 2 → ℂ) (c : Fin 2 → ℂ)
    (hc : c ∈ Submodule.span ℂ (Set.range X)) (l : Fin m)
    (f : FA2 m) (hf : f ∈ Submodule.span ℂ (Set.range (gmonC (m := m) X))) :
    AdmC c l f ∈ Submodule.span ℂ (Set.range (gmonC (m := m) X)) := by
  let S := Submodule.span ℂ (Set.range (gmonC (m := m) X))
  have hs (s : κ) : ∀ f ∈ S, AdmC (X s) l f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨α, rfl⟩ := hf
      rw [gmonC_succ]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add f g hf hg ihf ihg => simpa using S.add_mem ihf ihg
    | smul z f hf ih => simpa using S.smul_mem z ih
  have hc' : ∀ f ∈ S, AdmC c l f ∈ S := by
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨s, rfl⟩ := hc
      exact hs s
    | zero =>
      intro f hf
      simp [AdmC]
    | add c d hc hd ihc ihd =>
      intro f hf
      rw [AdmC_vec_add, LinearMap.add_apply]
      exact S.add_mem (ihc f hf) (ihd f hf)
    | smul z c hc ih =>
      intro f hf
      rw [AdmC_vec_smul, LinearMap.smul_apply]
      exact S.smul_mem _ (ih f hf)
  exact hc' f hf


/-- If the slot family `ℂ`-spans `ℂ²`, the monomials span `FA2 m`. -/
theorem single_mem_span_gmonC {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : κ → Fin 2 → ℂ)
    (hX : ∀ t : Fin 2, (Pi.single t 1 : Fin 2 → ℂ) ∈
      Submodule.span ℂ (Set.range X))
    (i : (Fin m → ℕ) × (Fin m → ℕ)) :
    Finsupp.single i (1 : ℂ) ∈
      Submodule.span ℂ (Set.range (gmonC (m := m) X)) := by
  classical
  let S := Submodule.span ℂ (Set.range (gmonC (m := m) X))
  have hbuild : ∀ α : Fin 2 → Fin m → ℕ,
      Finsupp.single (α 0, α 1) (1 : ℂ) ∈ S := by
    intro α
    induction α using exp_induction with
    | hzero =>
      apply Submodule.subset_span
      refine ⟨0, ?_⟩
      rw [gmonC_zero]
      rfl
    | hstep α t l ih =>
      have hc := gmonC_span_stable X (Pi.single t 1) (hX t) l _ ih
      fin_cases t
      · have hc' : (Real.sqrt ((α 0 l : ℝ) + 1) : ℂ) •
            Finsupp.single (Function.update (α 0) l (α 0 l + 1), α 1) 1 ∈ S := by
          simpa [AdmC, Pi.single_apply, copyL, adF, Finsupp.lsum_single,
            Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using hc
        have hn : (Real.sqrt ((α 0 l : ℝ) + 1) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
        have hh := S.smul_mem (Real.sqrt ((α 0 l : ℝ) + 1) : ℂ)⁻¹ hc'
        simpa [smul_smul, hn, bump] using hh
      · have hc' : (Real.sqrt ((α 1 l : ℝ) + 1) : ℂ) •
            Finsupp.single (α 0, Function.update (α 1) l (α 1 l + 1)) 1 ∈ S := by
          simpa [AdmC, Pi.single_apply, copyR, adF, Finsupp.lsum_single,
            Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using hc
        have hn : (Real.sqrt ((α 1 l : ℝ) + 1) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
        have hh := S.smul_mem (Real.sqrt ((α 1 l : ℝ) + 1) : ℂ)⁻¹ hc'
        simpa [smul_smul, hn, bump] using hh
  simpa using hbuild (![i.1, i.2] : Fin 2 → Fin m → ℕ)

/-! ### The `lambdaB` ladder and its eigenmodes -/

/-- The rotation acting on mode vectors under commutation with `lambdaB`. -/
def rotC (c : Fin 2 → ℂ) : Fin 2 → ℂ := ![-Complex.I * c 1, Complex.I * c 0]

private lemma comm_comp (A B C : FA2 m →ₗ[ℂ] FA2 m) :
    (A ∘ₗ B) ∘ₗ C - C ∘ₗ (A ∘ₗ B) =
      A ∘ₗ (B ∘ₗ C - C ∘ₗ B) + (A ∘ₗ C - C ∘ₗ A) ∘ₗ B := by
  simp only [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc]
  module

private lemma lambda_term_comm (c : Fin 2 → ℂ) (l k : Fin m) :
    (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k)) ∘ₗ AdmC c l -
      AdmC c l ∘ₗ (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k)) =
      if k = l then c 0 • copyR (adF k) - c 1 • copyL (adF k) else 0 := by
  classical
  have hL := ccrC (![1, 0]) c k l
  have hR := ccrC (![0, 1]) c k l
  have hLd := admC_admC_comm (![1, 0]) c k l
  have hRd := admC_admC_comm (![0, 1]) c k l
  simp only [AmC, AdmC, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_one, map_zero, one_smul, zero_smul, add_zero, zero_add,
    pairH, Fin.sum_univ_two, one_mul, zero_mul] at hL hR hLd hRd
  have hLd' : copyL (adF k) ∘ₗ AdmC c l - AdmC c l ∘ₗ copyL (adF k) = 0 := sub_eq_zero.mpr hLd
  have hRd' : copyR (adF k) ∘ₗ AdmC c l - AdmC c l ∘ₗ copyR (adF k) = 0 := sub_eq_zero.mpr hRd
  change copyL (aF k) ∘ₗ AdmC c l - AdmC c l ∘ₗ copyL (aF k) = _ at hL
  change copyR (aF k) ∘ₗ AdmC c l - AdmC c l ∘ₗ copyR (aF k) = _ at hR
  rw [LinearMap.sub_comp, LinearMap.comp_sub]
  have he : ∀ A B D E : FA2 m →ₗ[ℂ] FA2 m,
      (A - B) - (D - E) = (A - D) - (B - E) := by intros; module
  rw [he, comm_comp, comm_comp, hL, hR, hLd', hRd']
  by_cases h : k = l <;> simp [h, LinearMap.smul_comp, LinearMap.comp_smul]

/-- Ladder relation: `[lambdaB, AdmC c l] = AdmC (rotC c) l`. -/
theorem lambdaB_admC_comm (c : Fin 2 → ℂ) (l : Fin m) :
    lambdaB m ∘ₗ AdmC c l - AdmC c l ∘ₗ lambdaB m = AdmC (rotC c) l := by
  classical
  change (I • ∑ k, (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k))) ∘ₗ AdmC c l -
    AdmC c l ∘ₗ (I • ∑ k, (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k))) = _
  have he : (∑ k, (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k))) ∘ₗ AdmC c l -
      AdmC c l ∘ₗ (∑ k, (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k))) =
      c 0 • copyR (adF l) - c 1 • copyL (adF l) := by
    let T := fun k : Fin m => copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k)
    change (∑ k, T k) * AdmC c l - AdmC c l * (∑ k, T k) = _
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have h (k : Fin m) : T k * AdmC c l - AdmC c l * T k =
        if k = l then c 0 • copyR (adF k) - c 1 • copyL (adF k) else 0 :=
      lambda_term_comm c l k
    simp only [h]
    simp
  calc
    _ = I • ((∑ k, (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k))) ∘ₗ AdmC c l -
        AdmC c l ∘ₗ (∑ k, (copyL (aF k) ∘ₗ copyR (adF k) - copyL (adF k) ∘ₗ copyR (aF k)))) := by
      ext f q
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
        Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      rw [he]
      ext f q
      simp [AdmC, rotC, smul_sub, smul_smul]
      ring

/-- The two eigenmodes. -/
def cPlus : Fin 2 → ℂ := ![1, Complex.I]
def cMinus : Fin 2 → ℂ := ![1, -Complex.I]

@[simp] lemma rotC_cPlus : rotC cPlus = cPlus := by
  funext t
  fin_cases t <;> simp [rotC, cPlus, Complex.I_mul_I]
@[simp] lemma rotC_cMinus : rotC cMinus = fun t => (-1 : ℂ) * cMinus t := by
  funext t
  fin_cases t <;> simp [rotC, cMinus, Complex.I_mul_I]
@[simp] lemma pairH_plus_minus : pairH cPlus cMinus = 0 := by
  norm_num [pairH, cPlus, cMinus, Fin.sum_univ_two, Complex.I_mul_I]
@[simp] lemma pairH_minus_plus : pairH cMinus cPlus = 0 := by
  norm_num [pairH, cPlus, cMinus, Fin.sum_univ_two, Complex.I_mul_I]
@[simp] lemma pairH_plus_plus : pairH cPlus cPlus = 2 := by
  norm_num [pairH, cPlus, cMinus, Fin.sum_univ_two, Complex.I_mul_I]
@[simp] lemma pairH_minus_minus : pairH cMinus cMinus = 2 := by
  norm_num [pairH, cPlus, cMinus, Fin.sum_univ_two, Complex.I_mul_I]

/-- The eigenmode family. -/
def pmModes : Fin 2 → Fin 2 → ℂ := ![cPlus, cMinus]

lemma pmModes_spans (t : Fin 2) :
    (Pi.single t 1 : Fin 2 → ℂ) ∈ Submodule.span ℂ (Set.range pmModes) := by
  classical
  let coeff : Fin 2 → ℂ := if t = 0 then ![1/2, 1/2] else ![-I/2, I/2]
  have h : (∑ s, coeff s • pmModes s) ∈ Submodule.span ℂ (Set.range pmModes) := by
    apply Submodule.sum_mem
    intro s hs
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  convert h using 1
  ext j
  fin_cases t <;> fin_cases j <;>
    norm_num [coeff, pmModes, cPlus, cMinus, Fin.sum_univ_two, Pi.single_apply] <;> ring_nf
  simp

@[simp] theorem lambdaB_vac2 : lambdaB m (vac2 (m := m)) = 0 := by
  classical
  simp [lambdaB, vac2, aF, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

/-- `lambdaB` is diagonal on eigenmode monomials with eigenvalue `|α| − |β|`
(exponents `α` on `cPlus`, `β` on `cMinus`; `Fin 2`-slot family `pmModes`). -/
theorem lambdaB_gmonC (α : Fin 2 → Fin m → ℕ) :
    lambdaB m (gmonC pmModes α) =
      ((degB (α 0) : ℂ) - (degB (α 1) : ℂ)) • gmonC pmModes α := by
  classical
  induction α using exp_induction with
  | hzero => simp
  | hstep α s l ih =>
    have h := LinearMap.congr_fun (lambdaB_admC_comm (pmModes s) l) (gmonC pmModes α)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at h
    rw [← gmonC_succ, eq_add_of_sub_eq h, ih, map_smul, gmonC_succ]
    have hd := degB_update (α s) l (α s l + 1)
    have hd' : degB (Function.update (α s) l (α s l + 1)) = degB (α s) + 1 := by omega
    have hr : rotC (pmModes s) = (if s = 0 then (1 : ℂ) else -1) • pmModes s := by
      fin_cases s
      · change rotC cPlus = (1 : ℂ) • cPlus
        simp
      · change rotC cMinus = (-1 : ℂ) • cMinus
        exact rotC_cMinus
    rw [hr, AdmC_vec_smul, LinearMap.smul_apply, gmonC_succ]
    have he : ((if s = 0 then (1 : ℂ) else -1) +
        ((degB (α 0) : ℂ) - (degB (α 1) : ℂ))) =
        (degB (bump α s l 0) : ℂ) - (degB (bump α s l 1) : ℂ) := by
      simp only [degB_bump]
      fin_cases s <;> norm_num <;> ring
    rw [← add_smul, he]

/-! ### The swap–parity operator `W` -/

/-- Swap–parity on the coefficient space: swap the copies and multiply by the
parity of the second (pre-swap) copy. -/
noncomputable def Wsp (m : ℕ) : FA2 m →ₗ[ℂ] FA2 m :=
  Finsupp.lsum ℂ fun p => ((-1 : ℂ) ^ degB p.2) • Finsupp.lsingle (p.2, p.1)

@[simp] lemma Wsp_single (p : (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    Wsp m (Finsupp.single p z) = ((-1 : ℂ) ^ degB p.2) • Finsupp.single (p.2, p.1) z := by
  simp [Wsp, Finsupp.lsum_single]

@[simp] lemma Wsp_vac2 : Wsp m (vac2 (m := m)) = vac2 := by
  simp [vac2, degB]

/-- Intertwining: `W ∘ AdmC (c₀, c₁) = AdmC (−c₁, c₀) ∘ W`. -/
theorem Wsp_admC (c : Fin 2 → ℂ) (l : Fin m) :
    Wsp m ∘ₗ AdmC c l = AdmC ![-(c 1), c 0] l ∘ₗ Wsp m := by
  classical
  apply basis_ext
  intro p
  have hd := degB_update p.2 l (p.2 l + 1)
  have hd' : degB (Function.update p.2 l (p.2 l + 1)) = degB p.2 + 1 := by omega
  simp [AdmC, copyL, copyR, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Wsp_single,
    hd', pow_succ]
  ext q
  simp only [Finsupp.add_apply, Finsupp.neg_apply, Finsupp.single_apply]
  split_ifs <;> ring

/-- `W` acts diagonally on eigenmode monomials by `(−i)^{|α|} i^{|β|}`. -/
theorem Wsp_gmonC (α : Fin 2 → Fin m → ℕ) :
    Wsp m (gmonC pmModes α) =
      ((-Complex.I) ^ degB (α 0) * Complex.I ^ degB (α 1)) • gmonC pmModes α := by
  classical
  induction α using exp_induction with
  | hzero => simp [degB]
  | hstep α s l ih =>
    have h := LinearMap.congr_fun (Wsp_admC (pmModes s) l) (gmonC pmModes α)
    simp only [LinearMap.comp_apply] at h
    rw [← gmonC_succ, h, ih, map_smul]
    have hd := degB_update (α s) l (α s l + 1)
    have hd' : degB (Function.update (α s) l (α s l + 1)) = degB (α s) + 1 := by omega
    have hp : ![-(cPlus 1), cPlus 0] = (-I) • cPlus := by
      ext t; fin_cases t <;> simp [cPlus, Complex.I_mul_I]
    have hm : ![-(cMinus 1), cMinus 0] = I • cMinus := by
      ext t; fin_cases t <;> simp [cMinus, Complex.I_mul_I]
    have hr : ![-(pmModes s 1), pmModes s 0] =
        (if s = 0 then -I else I) • pmModes s := by
      fin_cases s
      · change ![-(cPlus 1), cPlus 0] = (-I) • cPlus
        exact hp
      · change ![-(cMinus 1), cMinus 0] = I • cMinus
        exact hm
    rw [hr, AdmC_vec_smul, LinearMap.smul_apply]
    have he : ((-I) ^ degB (α 0) * I ^ degB (α 1)) * (if s = 0 then -I else I) =
        (-I) ^ degB (bump α s l 0) * I ^ degB (bump α s l 1) := by
      simp only [degB_bump]
      fin_cases s <;> norm_num [pow_succ] <;> ring
    rw [smul_smul, he]

/-! ### Blocks: the kernel of `lambdaBlock` and `W` -/

/-- Two-copy homogeneous-component map into a degree block. -/
noncomputable def homogToBlock2 (n : ℕ) (f : FA2 m) :
    BlockSp (degB2 (m := m)) n :=
  WithLp.toLp 2 (fun i => f i.1)

private lemma fiber_sum {V : Type*} [AddCommMonoid V] {n : ℕ} {f : FA2 m}
    (hf : IsHomog2 n f) (H : ((Fin m → ℕ) × (Fin m → ℕ)) → ℂ → V)
    (hH : ∀ i, H i 0 = 0) :
    (∑ i : {i // degB2 i = n}, H i.1 (f i.1)) = f.sum H := by
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


lemma inner_homogToBlock2 {n : ℕ} {f : FA2 m} (hf : IsHomog2 n f) (g : FA2 m) :
    ⟪homogToBlock2 n f, homogToBlock2 n g⟫_ℂ = pairF2 f g := by

  classical
  simpa [PiLp.inner_apply, RCLike.inner_apply, homogToBlock2, pairF2, mul_comm] using
    fiber_sum hf (fun i z => star z * g i) (by simp)

lemma toBlock2_homogToBlock2 {T : FA2 m →ₗ[ℂ] FA2 m} (hT : ConservesDeg2 T)
    {n : ℕ} {f : FA2 m} (hf : IsHomog2 n f) :
    toBlock2 T n (homogToBlock2 n f) = homogToBlock2 n (T f) := by

  classical
  have _hconserves : ConservesDeg2 T := hT
  have hdecomp : (∑ i : {i // degB2 i = n}, f i.1 • Finsupp.single i.1 1) = f := by
    rw [fiber_sum hf (fun i z => z • Finsupp.single i 1) (by simp)]
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using f.sum_single
  ext i
  rw [toBlock2_apply]
  change (∑ j : {j // degB2 j = n}, f j.1 * (T (Finsupp.single j.1 1)) i.1) = (T f) i.1
  conv_rhs => rw [← hdecomp]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

/-- `W` conserves the total degree. -/
lemma conservesDeg2_Wsp (m : ℕ) : ConservesDeg2 (Wsp m) := by
  classical
  intro p q hq
  rw [Wsp_single] at hq
  have h := Finsupp.support_smul hq
  obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp h
  simp [degB2, Nat.add_comm]

private noncomputable def homogLM2 (n : ℕ) : FA2 m →ₗ[ℂ] BlockSp (degB2 (m := m)) n where
  toFun := homogToBlock2 n
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private lemma homogToBlock2_eq_zero {n d : ℕ} (hnd : d ≠ n) {f : FA2 m}
    (hf : IsHomog2 d f) : homogToBlock2 n f = 0 := by
  ext i
  change f i.1 = 0
  by_contra h
  exact hnd ((hf i.1 (Finsupp.mem_support_iff.mpr h)).symm.trans i.2)

private lemma block_gmonC_span (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    v ∈ Submodule.span ℂ (Set.range (fun β : Fin 2 → Fin m → ℕ =>
      homogToBlock2 n (gmonC pmModes β))) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun β : Fin 2 → Fin m → ℕ =>
      homogToBlock2 n (gmonC pmModes β)))
  have hi (i : {i // degB2 (m := m) i = n}) :
      homogToBlock2 n (Finsupp.single i.1 1) ∈ S := by
    have hh := single_mem_span_gmonC pmModes pmModes_spans i.1
    change homogLM2 n (Finsupp.single i.1 1) ∈ S
    exact Submodule.span_induction
      (p := fun x _ => homogLM2 n x ∈ S)
      (fun x hx => by obtain ⟨β, rfl⟩ := hx; exact Submodule.subset_span ⟨β, rfl⟩)
      (by simp)
      (fun x y _ _ ix iy => by simpa using S.add_mem ix iy)
      (fun z x _ ix => by simpa using S.smul_mem z ix) hh
  have hv : v = ∑ i, v i • homogToBlock2 n (Finsupp.single i.1 1) := by
    ext j
    change v j = (∑ i, v i • homogToBlock2 n (Finsupp.single i.1 1)) j
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

private lemma block_gmonC_eigen (n : ℕ) (β : Fin 2 → Fin m → ℕ) :
    lambdaBlock m n (homogToBlock2 n (gmonC pmModes β)) =
      ((degB (β 0) : ℂ) - (degB (β 1) : ℂ)) • homogToBlock2 n (gmonC pmModes β) := by
  classical
  by_cases hd : (∑ s, degB (β s)) = n
  · have hh : IsHomog2 n (gmonC pmModes β) := hd ▸ gmonC_homog _ _
    rw [lambdaBlock, toBlock2_homogToBlock2 (conservesDeg2_lambdaB m) hh, lambdaB_gmonC]
    rfl
  · rw [homogToBlock2_eq_zero hd (gmonC_homog _ _)]
    simp

/-- The balanced-monomial description of the kernel: the kernel of the
`lambdaB` block is spanned by the balanced eigenmode monomial blocks. -/
theorem ker_lambdaBlock_eq_span (m n : ℕ) :
    LinearMap.ker (lambdaBlock m n) =
      Submodule.span ℂ (Set.range (fun α :
          {α : Fin 2 → Fin m → ℕ // degB (α 0) = degB (α 1) ∧
            degB (α 0) + degB (α 1) = n} =>
        homogToBlock2 n (gmonC pmModes α.1))) := by
  classical
  let S := Submodule.span ℂ (Set.range (fun α :
      {α : Fin 2 → Fin m → ℕ // degB (α 0) = degB (α 1) ∧
        degB (α 0) + degB (α 1) = n} => homogToBlock2 n (gmonC pmModes α.1)))
  have hS : S ≤ LinearMap.ker (lambdaBlock m n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    change lambdaBlock m n (homogToBlock2 n (gmonC pmModes α.1)) = 0
    rw [block_gmonC_eigen, α.2.1, sub_self, zero_smul]
  have hbal (β : Fin 2 → Fin m → ℕ) (hb : degB (β 0) = degB (β 1)) :
      homogToBlock2 n (gmonC pmModes β) ∈ S := by
    by_cases hd : (∑ s, degB (β s)) = n
    · exact Submodule.subset_span ⟨⟨β, hb, by simpa [Fin.sum_univ_two] using hd⟩, rfl⟩
    · rw [homogToBlock2_eq_zero hd (gmonC_homog _ _)]
      exact S.zero_mem
  apply le_antisymm
  · intro v hv
    let r := v - S.starProjection v
    have hr : lambdaBlock m n r = 0 := by
      rw [show r = v - S.starProjection v from rfl, map_sub]
      rw [LinearMap.mem_ker.mp hv,
        LinearMap.mem_ker.mp (hS (S.starProjection_apply_mem v)), sub_self]
    have ho : ∀ β : Fin 2 → Fin m → ℕ,
        ⟪homogToBlock2 n (gmonC pmModes β), r⟫_ℂ = 0 := by
      intro β
      by_cases hb : degB (β 0) = degB (β 1)
      · exact inner_eq_zero_symm.mp
          (S.starProjection_inner_eq_zero v _ (hbal β hb))
      · have hl : ((degB (β 0) : ℂ) - (degB (β 1) : ℂ)) ≠ 0 := by
          exact sub_ne_zero.mpr (by exact_mod_cast hb)
        have hh := lambdaBlock_isSymmetric m n (homogToBlock2 n (gmonC pmModes β)) r
        rw [block_gmonC_eigen, hr, inner_smul_left, inner_zero_right] at hh
        exact (mul_eq_zero.mp hh).resolve_left (by simpa only [map_sub, map_natCast] using hl)
    have hall : ∀ x ∈ Submodule.span ℂ (Set.range (fun β : Fin 2 → Fin m → ℕ =>
        homogToBlock2 n (gmonC pmModes β))), ⟪x, r⟫_ℂ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨β, rfl⟩ := hx; exact ho β
      | zero => simp
      | add x y hx hy ix iy => rw [inner_add_left, ix, iy, add_zero]
      | smul z x hx ix => rw [inner_smul_left, ix, mul_zero]
    have hz : r = 0 := inner_self_eq_zero.mp (hall r (block_gmonC_span n r))
    have he : v = S.starProjection v := sub_eq_zero.mp hz
    rw [he]
    exact S.starProjection_apply_mem v
  · exact hS

/-- **`W` fixes the kernel of `Λ` pointwise** (per block). -/
theorem Wsp_eq_id_on_ker (m n : ℕ) (v : BlockSp (degB2 (m := m)) n)
    (hv : v ∈ LinearMap.ker (lambdaBlock m n)) :
    toBlock2 (Wsp m) n v = v := by
  classical
  rw [ker_lambdaBlock_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨α, rfl⟩ := hv
    have hd : (∑ s, degB (α.1 s)) = n := by simpa [Fin.sum_univ_two] using α.2.2
    have hh : IsHomog2 n (gmonC pmModes α.1) := by
      simpa only [hd] using (gmonC_homog (m := m) pmModes α.1)
    rw [toBlock2_homogToBlock2 (conservesDeg2_Wsp m) hh, Wsp_gmonC, α.2.1]
    have hi : (-I : ℂ) * I = 1 := by simp [Complex.I_mul_I]
    rw [← mul_pow, hi, one_pow, one_smul]
  | zero => simp
  | add x y hx hy ix iy => simp [map_add, ix, iy]
  | smul z x hx ix => simp [map_smul, ix]

/-! ### The ℓ²-level swap–parity operator -/

private lemma parity_norm (k : ℕ) (z : ℂ) : ‖((-1 : ℂ) ^ k) • z‖ = ‖z‖ := by
  simp [norm_pow]

lemma swapParity_mem (f : L2 ((Fin m → ℕ) × (Fin m → ℕ))) :
    Memℓp (fun p : (Fin m → ℕ) × (Fin m → ℕ) =>
      ((-1 : ℂ) ^ degB p.1) • f (p.2, p.1)) 2 := by
  apply mem_of_summable_normSq
  simp only [parity_norm]
  exact (Equiv.prodComm _ _).summable_iff.mpr (summable_normSq f)

lemma swapParity_norm (f g : L2 ((Fin m → ℕ) × (Fin m → ℕ)))
    (hg : ∀ p, g p = ((-1 : ℂ) ^ degB p.1) • f (p.2, p.1)) : ‖g‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  simp only [hg, parity_norm]
  exact (Equiv.prodComm _ _).tsum_eq (fun p => ‖f p‖ ^ (2 : ℝ≥0∞).toReal)

/-- The ℓ²-level swap–parity operator (an isometric involution up to parity
signs): `(WL f) (p, q) = (−1)^{degB p} f (q, p)`. -/
noncomputable def WL (m : ℕ) : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 →L[ℂ]
    lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 := by
  refine LinearMap.mkContinuous
    { toFun := fun f => ⟨fun p => ((-1 : ℂ) ^ degB p.1) • f (p.2, p.1), ?_⟩
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · exact swapParity_mem f
  · intro f g
    apply lp.ext
    funext p
    change ((-1 : ℂ) ^ degB p.1) * (f (p.2,p.1) + g (p.2,p.1)) = _
    exact mul_add _ _ _
  · intro z f
    apply lp.ext
    funext p
    change ((-1 : ℂ) ^ degB p.1) * (z * f (p.2,p.1)) = z * (((-1 : ℂ) ^ degB p.1) * f (p.2,p.1))
    ring
  · intro f
    rw [one_mul]
    exact (swapParity_norm f _ (fun _ => rfl)).le

@[simp] lemma WL_apply (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    WL m f p = ((-1 : ℂ) ^ degB p.1) • f (p.2, p.1) := rfl

lemma norm_WL_apply (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2) :
    ‖WL m f‖ = ‖f‖ := by
  exact swapParity_norm f (WL m f) (fun _ => rfl)

private lemma Wsp_block_apply (n : ℕ) (v : BlockSp (degB2 (m := m)) n)
    (i : {p // degB2 (m := m) p = n}) :
    toBlock2 (Wsp m) n v i =
      ((-1 : ℂ) ^ degB i.1.1) * v (swapFiber m n i) := by
  classical
  rw [toBlock2_apply]
  change (∑ j, v j * (Wsp m (Finsupp.single j.1 1)) i.1) = _
  rw [Finset.sum_eq_single (swapFiber m n i)]
  · simp [Wsp_single, swapFiber, mul_comm]
  · intro j hj hji
    have he : (j.1.2, j.1.1) ≠ i.1 := by
      intro he
      apply hji
      apply Subtype.ext
      exact congrArg Prod.swap he
    simp [Wsp_single, Ne.symm he]
  · simp

/-- **The purity-lemma interface**: `WL` fixes the image of the mean-zero
acceptance projection. -/
theorem WL_P0B (m : ℕ) : (WL m).comp (P0B m) = P0B m := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext p
  have happ (g : L2 ((Fin m → ℕ) × (Fin m → ℕ)))
      (q : (Fin m → ℕ) × (Fin m → ℕ)) {n : ℕ} (hq : degB2 q = n) :
      P0B m g q = (LinearMap.ker (lambdaBlock m n)).starProjection
        (blockProj degB2 g n) ⟨q,hq⟩ := by subst n; rfl
  let n := degB2 p
  let v := (LinearMap.ker (lambdaBlock m n)).starProjection (blockProj degB2 f n)
  have hv := (LinearMap.ker (lambdaBlock m n)).starProjection_apply_mem
    (blockProj degB2 f n)
  have h := congrArg (fun w : BlockSp (degB2 (m := m)) n => w ⟨p, rfl⟩)
    (Wsp_eq_id_on_ker m n v hv)
  rw [Wsp_block_apply] at h
  change ((-1 : ℂ) ^ degB p.1) • P0B m f (p.2, p.1) = P0B m f p
  rw [happ f p rfl, happ f (p.2, p.1) (n := n) (by simp [n, degB2, Nat.add_comm])]
  exact h

end GaussianTesting
