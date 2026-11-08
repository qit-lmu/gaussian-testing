module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Lambda

@[expose] public section

/-!
# Rotated creation and annihilation operators on three-copy Fock coefficients

This file builds the "centre-of-mass / difference mode" picture used in the
analysis of the bosonic coherent-state test (Lemma 6.6), entirely on the
finitely-supported coefficient space `FA3 m` from `Bosons/Lambda.lean`.

## Contents

* `Am c l`, `Adm c l` — annihilation/creation operators of the copy-combination
  mode with (rational!) coefficient vector `c : Fin 3 → ℚ` at mode `l`;
  `ccrM` is their CCR, with pairing `pairQ`.
* `vac3`, `monW` — the vacuum and creation-word monomials
  (`monW L = (∏ creators in L) vac3`).
* `gmon X α` — exponent-indexed monomials for a family `X : κ → (Fin 3 → ℚ)`
  of combination vectors ("slots") with exponents `α : κ → Fin m → ℕ`.
* `pairF` — the sesquilinear pairing `∑ conj (f i) * g i` on `FA3 m`, with
  `pairF_adm` (creation/annihilation adjointness).
* `gram_diag` — the ladder/Gram formula: if the cross pairings of the slots
  actually used are diagonal, then
  `pairF (gmon X α) (gmon Y β) = δ_{αβ} ∏_{s,l} (α s l)! ⟨X s, Y s⟩^(α s l)`.
* `single_mem_span_gmon` — completeness: if the standard basis of `ℚ³` lies in
  the `ℚ`-span of the slots, the monomials `gmon X α` span `FA3 m`.
* `gmon_homog` — `gmon X α` is `degB3`-homogeneous of degree `∑ s, degB (α s)`.
* `Mnum c` — the number operator `∑ l, Adm c l ∘ Am c l` of a combination
  mode, with eigenvalue action `Mnum_gmon` on monomials.
* Three frames indexed by the pairs (1,2), (1,3), and (2,3). Each has
  centre-of-mass direction `vVec`, retained direction `wVec a`, and lost
  difference mode `uVec a`. The three retained directions normalize to the
  manuscript vectors w₁₂, w₁₃, and w₂₃. Their `pairQ` inner products enter
  the Gram argument for the three kernel projections of `MopB a := Mnum (uVec a)`.

`Bosons/CoherentBlocks.lean` normalizes the block vectors obtained from
`gmon (frame a) ![p,q,0]`. Their inner products across different pair frames
are `(-3)^{|q|} / 6^{|q|} = (-1/2)^{|q|}`, as required by
`three_projection_gap_of_gram`.
-/

namespace GaussianTesting

open Finsupp Finset

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false

variable {m : ℕ}

/-! ### Combination modes and their CCR -/

/-- Annihilation operator of the copy-combination mode `c` at mode index `l`:
`c 0 • a_l⁽¹⁾ + c 1 • a_l⁽²⁾ + c 2 • a_l⁽³⁾`. -/
noncomputable def Am (c : Fin 3 → ℚ) (l : Fin m) : FA3 m →ₗ[ℂ] FA3 m :=
  (c 0 : ℂ) • copy1 (aF l) + (c 1 : ℂ) • copy2 (aF l) + (c 2 : ℂ) • copy3 (aF l)

/-- Creation operator of the copy-combination mode `c` at mode index `l`. -/
noncomputable def Adm (c : Fin 3 → ℚ) (l : Fin m) : FA3 m →ₗ[ℂ] FA3 m :=
  (c 0 : ℂ) • copy1 (adF l) + (c 1 : ℂ) • copy2 (adF l) + (c 2 : ℂ) • copy3 (adF l)

/-- Euclidean pairing of combination vectors. -/
def pairQ (c c' : Fin 3 → ℚ) : ℚ := ∑ t, c t * c' t

private lemma basis_ext {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    {S T : (ι →₀ ℂ) →ₗ[ℂ] V}
    (h : ∀ p, S (Finsupp.single p 1) = T (Finsupp.single p 1)) : S = T := by
  apply Finsupp.lhom_ext
  intro p c
  have he : Finsupp.single p c = c • Finsupp.single p 1 := by simp
  rw [he, map_smul, map_smul, h]

private lemma copy1_single (A : FA m →ₗ[ℂ] FA m)
    (p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    copy1 A (Finsupp.single p z) = z •
      Finsupp.lmapDomain ℂ ℂ (fun i => (i, p.2.1, p.2.2))
        (A (Finsupp.single p.1 1)) := by
  simp [copy1, Finsupp.lsum_single]

private lemma copy1_slice (A : FA m →ₗ[ℂ] FA m) (b c : Fin m → ℕ) (v : FA m) :
    copy1 A (Finsupp.lmapDomain ℂ ℂ (fun i => (i, b, c)) v) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (i, b, c)) (A v) := by
  have he : copy1 A ∘ₗ Finsupp.lmapDomain ℂ ℂ (fun i => (i, b, c)) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (i, b, c)) ∘ₗ A := by
    apply basis_ext
    intro p
    simp [copy1_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun he v

private lemma copy1_comp (A B : FA m →ₗ[ℂ] FA m) :
    copy1 A ∘ₗ copy1 B = copy1 (A ∘ₗ B) := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copy1_single, one_smul]
  exact copy1_slice A _ _ _

private lemma copy1_sub (A B : FA m →ₗ[ℂ] FA m) :
    copy1 (A - B) = copy1 A - copy1 B := by
  apply basis_ext
  intro p
  simp only [copy1_single, LinearMap.sub_apply, map_sub, one_smul]

private lemma copy1_id : copy1 (LinearMap.id : FA m →ₗ[ℂ] FA m) = LinearMap.id := by
  apply basis_ext
  intro p
  simp [copy1_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private lemma copy2_single (A : FA m →ₗ[ℂ] FA m)
    (p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    copy2 A (Finsupp.single p z) = z •
      Finsupp.lmapDomain ℂ ℂ (fun i => (p.1, i, p.2.2))
        (A (Finsupp.single p.2.1 1)) := by
  simp [copy2, Finsupp.lsum_single]

private lemma copy2_slice (A : FA m →ₗ[ℂ] FA m) (b c : Fin m → ℕ) (v : FA m) :
    copy2 A (Finsupp.lmapDomain ℂ ℂ (fun i => (b, i, c)) v) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (b, i, c)) (A v) := by
  have he : copy2 A ∘ₗ Finsupp.lmapDomain ℂ ℂ (fun i => (b, i, c)) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (b, i, c)) ∘ₗ A := by
    apply basis_ext
    intro p
    simp [copy2_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun he v

private lemma copy2_comp (A B : FA m →ₗ[ℂ] FA m) :
    copy2 A ∘ₗ copy2 B = copy2 (A ∘ₗ B) := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copy2_single, one_smul]
  exact copy2_slice A _ _ _

private lemma copy2_sub (A B : FA m →ₗ[ℂ] FA m) :
    copy2 (A - B) = copy2 A - copy2 B := by
  apply basis_ext
  intro p
  simp only [copy2_single, LinearMap.sub_apply, map_sub, one_smul]

private lemma copy2_id : copy2 (LinearMap.id : FA m →ₗ[ℂ] FA m) = LinearMap.id := by
  apply basis_ext
  intro p
  simp [copy2_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private lemma copy3_single (A : FA m →ₗ[ℂ] FA m)
    (p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    copy3 A (Finsupp.single p z) = z •
      Finsupp.lmapDomain ℂ ℂ (fun i => (p.1, p.2.1, i))
        (A (Finsupp.single p.2.2 1)) := by
  simp [copy3, Finsupp.lsum_single]

private lemma copy3_slice (A : FA m →ₗ[ℂ] FA m) (b c : Fin m → ℕ) (v : FA m) :
    copy3 A (Finsupp.lmapDomain ℂ ℂ (fun i => (b, c, i)) v) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (b, c, i)) (A v) := by
  have he : copy3 A ∘ₗ Finsupp.lmapDomain ℂ ℂ (fun i => (b, c, i)) =
      Finsupp.lmapDomain ℂ ℂ (fun i => (b, c, i)) ∘ₗ A := by
    apply basis_ext
    intro p
    simp [copy3_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun he v

private lemma copy3_comp (A B : FA m →ₗ[ℂ] FA m) :
    copy3 A ∘ₗ copy3 B = copy3 (A ∘ₗ B) := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copy3_single, one_smul]
  exact copy3_slice A _ _ _

private lemma copy3_sub (A B : FA m →ₗ[ℂ] FA m) :
    copy3 (A - B) = copy3 A - copy3 B := by
  apply basis_ext
  intro p
  simp only [copy3_single, LinearMap.sub_apply, map_sub, one_smul]

private lemma copy3_id : copy3 (LinearMap.id : FA m →ₗ[ℂ] FA m) = LinearMap.id := by
  apply basis_ext
  intro p
  simp [copy3_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private lemma copy12_comm (A B : FA m →ₗ[ℂ] FA m) :
    copy1 A ∘ₗ copy2 B = copy2 B ∘ₗ copy1 A := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copy1_single, copy2_single, one_smul]
  simp only [copy1, copy2, Finsupp.lsum_apply, Finsupp.lmapDomain_apply]
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

private lemma copy23_comm (A B : FA m →ₗ[ℂ] FA m) :
    copy2 A ∘ₗ copy3 B = copy3 B ∘ₗ copy2 A := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copy2_single, copy3_single, one_smul]
  simp only [copy2, copy3, Finsupp.lsum_apply, Finsupp.lmapDomain_apply]
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

private lemma copy13_comm (A B : FA m →ₗ[ℂ] FA m) :
    copy1 A ∘ₗ copy3 B = copy3 B ∘ₗ copy1 A := by
  apply basis_ext
  intro p
  simp only [LinearMap.comp_apply, copy1_single, copy3_single, one_smul]
  simp only [copy1, copy3, Finsupp.lsum_apply, Finsupp.lmapDomain_apply]
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


lemma pairQ_comm (c c' : Fin 3 → ℚ) : pairQ c c' = pairQ c' c := by
  unfold pairQ
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

lemma Adm_vec_add (c c' : Fin 3 → ℚ) (l : Fin m) :
    Adm (c + c') l = Adm c l + Adm c' l := by
  simp only [Adm, Pi.add_apply, Rat.cast_add, add_smul]
  module

lemma Adm_vec_smul (x : ℚ) (c : Fin 3 → ℚ) (l : Fin m) :
    Adm (x • c) l = (x : ℂ) • Adm c l := by
  simp only [Adm, Pi.smul_apply, smul_eq_mul, Rat.cast_mul, mul_smul, smul_add]

private lemma mode_ccr1 (l k : Fin m) :
    copy1 (aF l) ∘ₗ copy1 (adF k) - copy1 (adF k) ∘ₗ copy1 (aF l) =
      (if l = k then (1 : ℂ) else 0) • LinearMap.id := by
  classical
  rw [copy1_comp, copy1_comp, ← copy1_sub]
  by_cases h : l = k
  · subst k
    simp [ccr_same, copy1_id]
  · rw [(ccr_ne h).1]
    have hz : adF k ∘ₗ aF l - adF k ∘ₗ aF l = 0 := by
      ext v q
      simp
    rw [hz]
    simp only [h, ite_false, zero_smul]
    apply Finsupp.lhom_ext
    intro p z
    simp [copy1, Finsupp.lsum_single]

private lemma mode_ccr2 (l k : Fin m) :
    copy2 (aF l) ∘ₗ copy2 (adF k) - copy2 (adF k) ∘ₗ copy2 (aF l) =
      (if l = k then (1 : ℂ) else 0) • LinearMap.id := by
  classical
  rw [copy2_comp, copy2_comp, ← copy2_sub]
  by_cases h : l = k
  · subst k
    simp [ccr_same, copy2_id]
  · rw [(ccr_ne h).1]
    have hz : adF k ∘ₗ aF l - adF k ∘ₗ aF l = 0 := by
      ext v q
      simp
    rw [hz]
    simp only [h, ite_false, zero_smul]
    apply Finsupp.lhom_ext
    intro p z
    simp [copy2, Finsupp.lsum_single]

private lemma mode_ccr3 (l k : Fin m) :
    copy3 (aF l) ∘ₗ copy3 (adF k) - copy3 (adF k) ∘ₗ copy3 (aF l) =
      (if l = k then (1 : ℂ) else 0) • LinearMap.id := by
  classical
  rw [copy3_comp, copy3_comp, ← copy3_sub]
  by_cases h : l = k
  · subst k
    simp [ccr_same, copy3_id]
  · rw [(ccr_ne h).1]
    have hz : adF k ∘ₗ aF l - adF k ∘ₗ aF l = 0 := by
      ext v q
      simp
    rw [hz]
    simp only [h, ite_false, zero_smul]
    apply Finsupp.lhom_ext
    intro p z
    simp [copy3, Finsupp.lsum_single]

/-- CCR for combination modes: `[Am c l, Adm c' l'] = δ_{l l'} ⟨c, c'⟩`. -/
theorem ccrM (c c' : Fin 3 → ℚ) (l l' : Fin m) :
    Am c l ∘ₗ Adm c' l' - Adm c' l' ∘ₗ Am c l
      = (if l = l' then ((pairQ c c' : ℚ) : ℂ) else 0) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  have h1 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (mode_ccr1 l l')
  have h2 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (mode_ccr2 l l')
  have h3 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (mode_ccr3 l l')
  have h12 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (copy12_comm (aF l) (adF l'))
  have h21 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) ((copy12_comm (adF l') (aF l)).symm)
  have h13 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (copy13_comm (aF l) (adF l'))
  have h31 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) ((copy13_comm (adF l') (aF l)).symm)
  have h23 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (copy23_comm (aF l) (adF l'))
  have h32 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) ((copy23_comm (adF l') (aF l)).symm)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at *
  simp only [Am, Adm, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, pairQ, Fin.sum_univ_three,
    Rat.cast_add, Rat.cast_mul]
  split_ifs at * <;>
    linear_combination
      (c 0 : ℂ) * (c' 0 : ℂ) * h1 +
      (c 1 : ℂ) * (c' 1 : ℂ) * h2 +
      (c 2 : ℂ) * (c' 2 : ℂ) * h3 +
      (c 0 : ℂ) * (c' 1 : ℂ) * h12 +
      (c 0 : ℂ) * (c' 2 : ℂ) * h13 +
      (c 1 : ℂ) * (c' 0 : ℂ) * h21 +
      (c 1 : ℂ) * (c' 2 : ℂ) * h23 +
      (c 2 : ℂ) * (c' 0 : ℂ) * h31 +
      (c 2 : ℂ) * (c' 1 : ℂ) * h32

/-- Creation operators commute. -/
theorem adm_adm_comm (c c' : Fin 3 → ℚ) (l l' : Fin m) :
    Adm c l ∘ₗ Adm c' l' = Adm c' l' ∘ₗ Adm c l := by
  classical
  have hc : adF l ∘ₗ adF l' = adF l' ∘ₗ adF l := by
    by_cases h : l = l'
    · subst l'; rfl
    · exact (ccr_ne h).2.2
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  have h1 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (show copy1 (adF l) ∘ₗ copy1 (adF l') = copy1 (adF l') ∘ₗ copy1 (adF l) by rw [copy1_comp, copy1_comp, hc])
  have h2 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (show copy2 (adF l) ∘ₗ copy2 (adF l') = copy2 (adF l') ∘ₗ copy2 (adF l) by rw [copy2_comp, copy2_comp, hc])
  have h3 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (show copy3 (adF l) ∘ₗ copy3 (adF l') = copy3 (adF l') ∘ₗ copy3 (adF l) by rw [copy3_comp, copy3_comp, hc])
  have h12 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (copy12_comm (adF l) (adF l'))
  have h21 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) ((copy12_comm (adF l') (adF l)).symm)
  have h13 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (copy13_comm (adF l) (adF l'))
  have h31 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) ((copy13_comm (adF l') (adF l)).symm)
  have h23 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) (copy23_comm (adF l) (adF l'))
  have h32 := congrArg (fun T : FA3 m →ₗ[ℂ] FA3 m => T v q) ((copy23_comm (adF l') (adF l)).symm)
  simp only [LinearMap.comp_apply] at *
  simp only [Adm, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  linear_combination
      (c 0 : ℂ) * (c' 0 : ℂ) * h1 +
      (c 1 : ℂ) * (c' 1 : ℂ) * h2 +
      (c 2 : ℂ) * (c' 2 : ℂ) * h3 +
      (c 0 : ℂ) * (c' 1 : ℂ) * h12 +
      (c 0 : ℂ) * (c' 2 : ℂ) * h13 +
      (c 1 : ℂ) * (c' 0 : ℂ) * h21 +
      (c 1 : ℂ) * (c' 2 : ℂ) * h23 +
      (c 2 : ℂ) * (c' 0 : ℂ) * h31 +
      (c 2 : ℂ) * (c' 1 : ℂ) * h32

/-! ### Vacuum and monomials -/

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

private lemma support_image_degree (T : FA3 m →ₗ[ℂ] FA3 m) (a b : ℕ)
    (hT : ∀ p q, q ∈ (T (Finsupp.single p 1)).support →
      degB3 q + a = degB3 p + b)
    (f : FA3 m) (q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))
    (hq : q ∈ (T f).support) :
    ∃ p ∈ f.support, degB3 q + a = degB3 p + b := by
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
    ∀ p q, q ∈ (copy1 (adF l) (Finsupp.single p 1)).support →
      degB3 q = degB3 p + 1 := by
  classical
  intro p q h
  simp only [copy1, adF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hd := degB_update p.1 l (p.1 l + 1)
  dsimp [degB3]
  omega

private lemma shift_2_adF (l : Fin m) :
    ∀ p q, q ∈ (copy2 (adF l) (Finsupp.single p 1)).support →
      degB3 q = degB3 p + 1 := by
  classical
  intro p q h
  simp only [copy2, adF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hd := degB_update p.2.1 l (p.2.1 l + 1)
  dsimp [degB3]
  omega

private lemma shift_3_adF (l : Fin m) :
    ∀ p q, q ∈ (copy3 (adF l) (Finsupp.single p 1)).support →
      degB3 q = degB3 p + 1 := by
  classical
  intro p q h
  simp only [copy3, adF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hd := degB_update p.2.2 l (p.2.2 l + 1)
  dsimp [degB3]
  omega

private lemma shift_1_aF (l : Fin m) :
    ∀ p q, q ∈ (copy1 (aF l) (Finsupp.single p 1)).support →
      degB3 q + 1 = degB3 p := by
  classical
  intro p q h
  simp only [copy1, aF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.1 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hd := degB_update p.1 l (p.1 l - 1)
  dsimp [degB3]
  omega

private lemma shift_2_aF (l : Fin m) :
    ∀ p q, q ∈ (copy2 (aF l) (Finsupp.single p 1)).support →
      degB3 q + 1 = degB3 p := by
  classical
  intro p q h
  simp only [copy2, aF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.2.1 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hd := degB_update p.2.1 l (p.2.1 l - 1)
  dsimp [degB3]
  omega

private lemma shift_3_aF (l : Fin m) :
    ∀ p q, q ∈ (copy3 (aF l) (Finsupp.single p 1)).support →
      degB3 q + 1 = degB3 p := by
  classical
  intro p q h
  simp only [copy3, aF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    Finsupp.lmapDomain_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.2.2 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have hd := degB_update p.2.2 l (p.2.2 l - 1)
  dsimp [degB3]
  omega

private lemma shift_Adm (c : Fin 3 → ℚ) (l : Fin m) :
    ∀ p q, q ∈ (Adm c l (Finsupp.single p 1)).support →
      degB3 q = degB3 p + 1 := by
  intro p q h
  simp only [Adm, LinearMap.add_apply, LinearMap.smul_apply] at h
  rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
  · rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
    · exact shift_1_adF l p q (Finsupp.support_smul h)
    · exact shift_2_adF l p q (Finsupp.support_smul h)
  · exact shift_3_adF l p q (Finsupp.support_smul h)

private lemma shift_Am (c : Fin 3 → ℚ) (l : Fin m) :
    ∀ p q, q ∈ (Am c l (Finsupp.single p 1)).support →
      degB3 q + 1 = degB3 p := by
  intro p q h
  simp only [Am, LinearMap.add_apply, LinearMap.smul_apply] at h
  rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
  · rcases Finset.mem_union.mp (Finsupp.support_add h) with h | h
    · exact shift_1_aF l p q (Finsupp.support_smul h)
    · exact shift_2_aF l p q (Finsupp.support_smul h)
  · exact shift_3_aF l p q (Finsupp.support_smul h)

/-- The three-copy vacuum coefficient vector. -/
noncomputable def vac3 : FA3 m :=
  Finsupp.single ((fun _ => 0), (fun _ => 0), (fun _ => 0)) 1

theorem Am_vac3 (c : Fin 3 → ℚ) (l : Fin m) : Am c l (vac3 (m := m)) = 0 := by
  classical
  simp [Am, vac3, copy1, copy2, copy3, aF, Finsupp.lsum_single]

/-- The monomial vector of a creation word: apply the creators listed in `L`
(leftmost outermost) to the vacuum. -/
noncomputable def monW (L : List ((Fin 3 → ℚ) × Fin m)) : FA3 m :=
  ((L.map fun x => Adm x.1 x.2).prod : FA3 m →ₗ[ℂ] FA3 m) vac3

@[simp] theorem monW_nil : monW ([] : List ((Fin 3 → ℚ) × Fin m)) = vac3 := by
  simp [monW]

theorem monW_cons (x : (Fin 3 → ℚ) × Fin m) (L : List ((Fin 3 → ℚ) × Fin m)) :
    monW (x :: L) = Adm x.1 x.2 (monW L) := by
  simp [monW, Module.End.mul_apply]

/-- Monomials only depend on the multiset of creators (creators commute). -/
theorem monW_perm {L L' : List ((Fin 3 → ℚ) × Fin m)} (h : L.Perm L') :
    monW L = monW L' := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [monW_cons, ih]
  | swap x y L =>
    simp only [monW_cons]
    change (Adm y.1 y.2 ∘ₗ Adm x.1 x.2) (monW L) =
      (Adm x.1 x.2 ∘ₗ Adm y.1 y.2) (monW L)
    exact LinearMap.congr_fun (adm_adm_comm y.1 x.1 y.2 x.2) (monW L)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- One ladder step: commute an annihilator through the leading creator. -/
theorem Am_monW_cons (c : Fin 3 → ℚ) (l : Fin m) (x : (Fin 3 → ℚ) × Fin m)
    (L : List ((Fin 3 → ℚ) × Fin m)) :
    Am c l (monW (x :: L)) =
      (if l = x.2 then ((pairQ c x.1 : ℚ) : ℂ) else 0) • monW L
        + Adm x.1 x.2 (Am c l (monW L)) := by
  have h := LinearMap.congr_fun (ccrM c x.1 l x.2) (monW L)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at h
  rw [monW_cons]
  exact eq_add_of_sub_eq h

/-! ### Exponent-indexed monomials -/

section Gmon

variable {κ : Type*} [fintypeκ : Fintype κ] [decidableEqκ : DecidableEq κ]

/-- The canonical creation word of a slot family `X` with exponents `α`. -/
noncomputable def expWord (X : κ → Fin 3 → ℚ) (α : κ → Fin m → ℕ) :
    List ((Fin 3 → ℚ) × Fin m) :=
  (Finset.univ : Finset κ).toList.flatMap fun s =>
    (List.finRange m).flatMap fun l => List.replicate (α s l) (X s, l)

/-- Exponent-indexed monomial: `∏_{s,l} (Adm (X s) l)^(α s l)` on the vacuum. -/
noncomputable def gmon (X : κ → Fin 3 → ℚ) (α : κ → Fin m → ℕ) : FA3 m :=
  monW (expWord X α)

omit fintypeκ decidableEqκ in
@[simp] theorem gmon_zero [Fintype κ] [DecidableEq κ] (X : κ → Fin 3 → ℚ) :
    gmon (m := m) X 0 = vac3 := by
  have h : expWord (m := m) X 0 = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro s hs
    apply List.flatMap_eq_nil_iff.mpr
    intro l hl
    simp
  simp [gmon, h]

/-- Exponent bump at slot `s₀`, mode `l`. -/
def bump (α : κ → Fin m → ℕ) (s₀ : κ) (l : Fin m) : κ → Fin m → ℕ :=
  Function.update α s₀ (Function.update (α s₀) l (α s₀ l + 1))

/-- Exponent decrement (ℕ-truncated) at slot `s₀`, mode `l`. -/
def debump (α : κ → Fin m → ℕ) (s₀ : κ) (l : Fin m) : κ → Fin m → ℕ :=
  Function.update α s₀ (Function.update (α s₀) l (α s₀ l - 1))

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

private lemma expWord_bump_perm (X : κ → Fin 3 → ℚ)
    (α : κ → Fin m → ℕ) (s : κ) (l : Fin m) :
    (expWord X (bump α s l)).Perm ((X s, l) :: expWord X α) := by
  unfold expWord
  apply flatMap_bump_perm _ (Finset.nodup_toList _) s (by simp)
  · intro t ht hts
    simp [bump, Function.update_of_ne hts]
  · apply flatMap_bump_perm _ (List.nodup_finRange _) l (by simp)
    · intro k hk hkl
      simp [bump, Function.update_of_ne hkl]
    · simp [bump, List.replicate_succ]

/-- Applying a slot creator bumps the exponent. -/
theorem gmon_succ (X : κ → Fin 3 → ℚ) (α : κ → Fin m → ℕ) (s₀ : κ) (l : Fin m) :
    Adm (X s₀) l (gmon X α) = gmon X (bump α s₀ l) := by
  exact (monW_cons (X s₀, l) (expWord X α)).symm.trans
    (monW_perm (expWord_bump_perm X α s₀ l)).symm

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

private lemma exp_orth_bump {c : Fin 3 → ℚ} {X : κ → Fin 3 → ℚ}
    {α : κ → Fin m → ℕ} {s t : κ} {k : Fin m}
    (h : ∀ u, u ≠ s → bump α t k u ≠ 0 → pairQ c (X u) = 0) :
    ∀ u, u ≠ s → α u ≠ 0 → pairQ c (X u) = 0 := by
  intro u hus hu
  apply h u hus
  intro hz
  apply hu
  ext j
  have hj := congrFun hz j
  rw [bump_apply] at hj
  simp only [Pi.zero_apply] at hj ⊢
  omega

private lemma Am_gmon_cross (c : Fin 3 → ℚ) (X : κ → Fin 3 → ℚ)
    (α : κ → Fin m → ℕ) (s : κ) (l : Fin m)
    (horth : ∀ t, t ≠ s → α t ≠ 0 → pairQ c (X t) = 0) :
    Am c l (gmon X α) =
      ((α s l : ℂ) * (pairQ c (X s) : ℂ)) • gmon X (debump α s l) := by
  induction α using exp_induction with
  | hzero =>
    simp [gmon_zero, Am_vac3]
  | hstep α t k ih =>
    have ho := exp_orth_bump horth
    have ladder : Am c l (gmon X (bump α t k)) =
        (if l = k then (pairQ c (X t) : ℂ) else 0) • gmon X α +
          Adm (X t) k (Am c l (gmon X α)) := by
      rw [← gmon_succ]
      exact Am_monW_cons c l (X t, k) (expWord X α)
    rw [ladder, ih ho, map_smul, gmon_succ]
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
    · have hpair : pairQ c (X t) = 0 := by
        apply horth t ht
        intro hz
        have hh := congrFun hz k
        simp [bump] at hh
      rw [debump_bump_ne α s t l k (Or.inl (Ne.symm ht)), bump_apply]
      simp [Ne.symm ht, hpair]

/-- Applying a slot annihilator, when the cross pairings with all *used* other
slots vanish, decrements the exponent with the ladder coefficient. -/
theorem Am_gmon (X : κ → Fin 3 → ℚ) (α : κ → Fin m → ℕ) (s₀ : κ)
    (horth : ∀ t, t ≠ s₀ → α t ≠ 0 → pairQ (X s₀) (X t) = 0) (l : Fin m) :
    Am (X s₀) l (gmon X α) =
      (((α s₀ l : ℚ) * pairQ (X s₀) (X s₀) : ℚ) : ℂ) • gmon X (debump α s₀ l) := by
  simpa using Am_gmon_cross (X s₀) X α s₀ l horth

end Gmon

/-! ### The pairing and the Gram formula -/

/-- The standard sesquilinear pairing on `FA3 m` (finite sums; agrees with the
`ℓ²` inner product on homogeneous blocks). -/
def pairF (f g : FA3 m) : ℂ := f.sum fun i z => (starRingEnd ℂ) z * g i

theorem pairF_add_left (f f' g : FA3 m) :
    pairF (f + f') g = pairF f g + pairF f' g := by
  classical
  unfold pairF
  exact Finsupp.sum_add_index (by simp) (by intros; simp [add_mul])

theorem pairF_add_right (f g g' : FA3 m) :
    pairF f (g + g') = pairF f g + pairF f g' := by
  classical
  simp [pairF, Finsupp.sum, mul_add, Finset.sum_add_distrib]

theorem pairF_smul_left (z : ℂ) (f g : FA3 m) :
    pairF (z • f) g = (starRingEnd ℂ) z * pairF f g := by
  classical
  unfold pairF
  rw [Finsupp.sum_smul_index' (by simp)]
  simp [Finsupp.sum, map_mul, mul_assoc, Finset.mul_sum]

theorem pairF_smul_right (z : ℂ) (f g : FA3 m) :
    pairF f (z • g) = z * pairF f g := by
  classical
  simp [pairF, Finsupp.sum, Finset.mul_sum, mul_left_comm]

@[simp] theorem pairF_zero_left (g : FA3 m) : pairF 0 g = 0 := by
  simp [pairF]

@[simp] theorem pairF_zero_right (f : FA3 m) : pairF f 0 = 0 := by
  simp [pairF]

@[simp] theorem pairF_vac3_vac3 : pairF (vac3 (m := m)) vac3 = 1 := by
  classical
  simp [pairF, vac3]

private lemma pairF_single_left (p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))
    (z : ℂ) (g : FA3 m) : pairF (Finsupp.single p z) g = star z * g p := by
  classical
  simp [pairF, Finsupp.sum_single_index]

private lemma pairF_single_right (f : FA3 m)
    (q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) (z : ℂ) :
    pairF f (Finsupp.single q z) = star (f q) * z := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp [pairF_add_left, hf, hg, add_mul]
  | single p w =>
    simp [pairF_single_left, Finsupp.single_apply, eq_comm]
    split_ifs <;> simp_all

private lemma pairF_adj (A B : FA3 m →ₗ[ℂ] FA3 m)
    (h : ∀ p q, (A (Finsupp.single p 1)) q =
      star ((B (Finsupp.single q 1)) p)) (f g : FA3 m) :
    pairF (A f) g = pairF f (B g) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [map_add, pairF_add_left, hf, hf']
  | single p z =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp [map_add, pairF_add_right, hg, hg']
    | single q w =>
      have hz : Finsupp.single p z = z • Finsupp.single p 1 := by simp
      have hw : Finsupp.single q w = w • Finsupp.single q 1 := by simp
      rw [pairF_single_right, hw, map_smul, hz, map_smul,
        pairF_smul_left, pairF_single_left]
      simp [h, mul_comm, mul_left_comm]

private lemma aF_entry (l : Fin m) (p q : Fin m → ℕ) :
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

private lemma adF_entry (l : Fin m) (p q : Fin m → ℕ) :
    (adF l (Finsupp.single p 1)) q = star ((aF l (Finsupp.single q 1)) p) := by
  simpa only [star_star] using congrArg star (aF_entry l q p).symm

private lemma entry_1_aF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (copy1 (aF l) (Finsupp.single p 1)) q =
      ((aF l (Finsupp.single p.1 1)) q.1) * ((Finsupp.single p.2.1 (1 : ℂ)) q.2.1) * ((Finsupp.single p.2.2 (1 : ℂ)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, aF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma entry_1_adF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (copy1 (adF l) (Finsupp.single p 1)) q =
      ((adF l (Finsupp.single p.1 1)) q.1) * ((Finsupp.single p.2.1 (1 : ℂ)) q.2.1) * ((Finsupp.single p.2.2 (1 : ℂ)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma entry_2_aF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (copy2 (aF l) (Finsupp.single p 1)) q =
      ((Finsupp.single p.1 (1 : ℂ)) q.1) * ((aF l (Finsupp.single p.2.1 1)) q.2.1) * ((Finsupp.single p.2.2 (1 : ℂ)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy2, aF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma entry_2_adF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (copy2 (adF l) (Finsupp.single p 1)) q =
      ((Finsupp.single p.1 (1 : ℂ)) q.1) * ((adF l (Finsupp.single p.2.1 1)) q.2.1) * ((Finsupp.single p.2.2 (1 : ℂ)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy2, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma entry_3_aF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (copy3 (aF l) (Finsupp.single p 1)) q =
      ((Finsupp.single p.1 (1 : ℂ)) q.1) * ((Finsupp.single p.2.1 (1 : ℂ)) q.2.1) * ((aF l (Finsupp.single p.2.2 1)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy3, aF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma entry_3_adF (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (copy3 (adF l) (Finsupp.single p 1)) q =
      ((Finsupp.single p.1 (1 : ℂ)) q.1) * ((Finsupp.single p.2.1 (1 : ℂ)) q.2.1) * ((adF l (Finsupp.single p.2.2 1)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy3, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

private lemma single_star_symm {ι : Type*} (p q : ι) :
    (Finsupp.single p (1 : ℂ)) q = star ((Finsupp.single q (1 : ℂ)) p) := by
  classical
  simp [Finsupp.single_apply, eq_comm]

private lemma pairF_copy1_adm (l : Fin m) (f g : FA3 m) :
    pairF (copy1 (adF l) f) g = pairF f (copy1 (aF l) g) := by
  apply pairF_adj
  intro p q
  rw [entry_1_adF, entry_1_aF, adF_entry, single_star_symm p.2.1 q.2.1, single_star_symm p.2.2 q.2.2]
  simp only [star_mul]
  ring

private lemma pairF_copy2_adm (l : Fin m) (f g : FA3 m) :
    pairF (copy2 (adF l) f) g = pairF f (copy2 (aF l) g) := by
  apply pairF_adj
  intro p q
  rw [entry_2_adF, entry_2_aF, adF_entry, single_star_symm p.1 q.1, single_star_symm p.2.2 q.2.2]
  simp only [star_mul]
  ring

private lemma pairF_copy3_adm (l : Fin m) (f g : FA3 m) :
    pairF (copy3 (adF l) f) g = pairF f (copy3 (aF l) g) := by
  apply pairF_adj
  intro p q
  rw [entry_3_adF, entry_3_aF, adF_entry, single_star_symm p.1 q.1, single_star_symm p.2.1 q.2.1]
  simp only [star_mul]
  ring

/-- Adjointness of creation and annihilation for the pairing (the coefficient
vectors are rational, hence conjugation-invariant). -/
theorem pairF_adm (c : Fin 3 → ℚ) (l : Fin m) (f g : FA3 m) :
    pairF (Adm c l f) g = pairF f (Am c l g) := by
  simp [Adm, Am, pairF_add_left, pairF_add_right, pairF_smul_left,
    pairF_smul_right, pairF_copy1_adm, pairF_copy2_adm, pairF_copy3_adm]

section Gram

variable {κ : Type*} [fintypeκ : Fintype κ] [decidableEqκ : DecidableEq κ]

private lemma pairF_symm (f g : FA3 m) : pairF f g = star (pairF g f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp [pairF_add_left, pairF_add_right, hf, hf']
  | single p z =>
    rw [pairF_single_left, pairF_single_right]
    simp [star_mul, mul_comm]

private lemma pairF_vac_adm (c : Fin 3 → ℚ) (l : Fin m) (f : FA3 m) :
    pairF vac3 (Adm c l f) = 0 := by
  rw [pairF_symm, pairF_adm, Am_vac3, pairF_zero_right, star_zero]

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

private lemma pairF_vac_gmon (Y : κ → Fin 3 → ℚ) (β : κ → Fin m → ℕ) :
    pairF vac3 (gmon Y β) = if β = 0 then 1 else 0 := by
  induction β using exp_induction with
  | hzero => simp
  | hstep β s l ih =>
    rw [← gmon_succ, pairF_vac_adm]
    simp [bump_not_zero]

private lemma gram_product_bump (X Y : κ → Fin 3 → ℚ)
    (α : κ → Fin m → ℕ) (s : κ) (l : Fin m) :
    (∏ t, ∏ k, ((bump α s l t k).factorial : ℚ) *
      pairQ (X t) (Y t) ^ (bump α s l t k)) =
    ((α s l + 1 : ℕ) : ℚ) * pairQ (X s) (Y s) *
      (∏ t, ∏ k, ((α t k).factorial : ℚ) * pairQ (X t) (Y t) ^ (α t k)) := by
  classical
  let F := fun (t : κ) (k : Fin m) (n : ℕ) =>
    (n.factorial : ℚ) * pairQ (X t) (Y t) ^ n
  change (∏ t, ∏ k, F t k (bump α s l t k)) =
    ((α s l + 1 : ℕ) : ℚ) * pairQ (X s) (Y s) * (∏ t, ∏ k, F t k (α t k))
  rw [← Finset.mul_prod_erase Finset.univ (fun t => ∏ k, F t k (bump α s l t k)) (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun t => ∏ k, F t k (α t k)) (Finset.mem_univ s)]
  have he : (∏ t ∈ Finset.univ.erase s, ∏ k, F t k (bump α s l t k)) =
      ∏ t ∈ Finset.univ.erase s, ∏ k, F t k (α t k) := by
    apply Finset.prod_congr rfl
    intro t ht
    simp [bump, Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  rw [he]
  have hi : (∏ k, F s k (bump α s l s k)) =
      ((α s l + 1 : ℕ) : ℚ) * pairQ (X s) (Y s) * ∏ k, F s k (α s k) := by
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

/-- The Gram/Wick formula for monomials of two slot families whose *used*
cross pairings are diagonal. -/
theorem gram_diag (X Y : κ → Fin 3 → ℚ) (α β : κ → Fin m → ℕ)
    (hdiag : ∀ s t : κ, s ≠ t → α s ≠ 0 → β t ≠ 0 → pairQ (X s) (Y t) = 0) :
    pairF (gmon (m := m) X α) (gmon Y β) =
      if α = β then
        ((∏ s, ∏ l, ((α s l).factorial : ℚ) * pairQ (X s) (Y s) ^ (α s l)) : ℂ)
      else 0 := by
  classical
  induction α using exp_induction generalizing β with
  | hzero =>
    rw [gmon_zero, pairF_vac_gmon]
    by_cases hβ : β = 0
    · subst β
      simp
    · simp [hβ, Ne.symm hβ]
  | hstep α s l ih =>
    have hused : bump α s l s ≠ 0 := by
      intro hz
      have hh := congrFun hz l
      simp [bump] at hh
    have horth : ∀ t, t ≠ s → β t ≠ 0 → pairQ (X s) (Y t) = 0 := by
      intro t hts ht
      exact hdiag s t (Ne.symm hts) hused ht
    have hdiag' : ∀ u t, u ≠ t → α u ≠ 0 →
        debump β s l t ≠ 0 → pairQ (X u) (Y t) = 0 := by
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
    rw [← gmon_succ, pairF_adm, Am_gmon_cross (X s) Y β s l horth,
      pairF_smul_right, ih _ hdiag']
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
        exact_mod_cast (gram_product_bump X Y α s l).symm
      · have hne : bump α s l ≠ β := by
          intro hh
          apply he
          rw [← hh, debump_bump]
        simp [he, hne]

end Gram

/-! ### Homogeneity -/

/-- `degB3`-homogeneity of a coefficient vector. -/
def IsHomog3 (n : ℕ) (f : FA3 m) : Prop := ∀ i ∈ f.support, degB3 i = n

theorem isHomog3_adm {n : ℕ} {f : FA3 m} (hf : IsHomog3 n f)
    (c : Fin 3 → ℚ) (l : Fin m) : IsHomog3 (n + 1) (Adm c l f) := by
  intro q hq
  obtain ⟨p, hp, hd⟩ := support_image_degree (Adm c l) 0 1
    (by simpa using shift_Adm c l) f q hq
  simpa [hf p hp] using hd

theorem gmon_homog {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : κ → Fin 3 → ℚ) (α : κ → Fin m → ℕ) :
    IsHomog3 (∑ s, degB (α s)) (gmon (m := m) X α) := by
  induction α using exp_induction with
  | hzero =>
    simp only [gmon_zero]
    intro i hi
    obtain ⟨he, hc⟩ := (Finsupp.mem_support_single _ _ _).mp hi
    subst i
    simp [degB3, degB]
  | hstep α s l ih =>
    rw [← gmon_succ]
    simpa only [degB, exp_total_bump] using isHomog3_adm ih (X s) l

/-! ### Completeness -/

private lemma gmon_span_stable {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : κ → Fin 3 → ℚ) (c : Fin 3 → ℚ)
    (hc : c ∈ Submodule.span ℚ (Set.range X)) (l : Fin m)
    (f : FA3 m) (hf : f ∈ Submodule.span ℂ (Set.range (gmon (m := m) X))) :
    Adm c l f ∈ Submodule.span ℂ (Set.range (gmon (m := m) X)) := by
  let S := Submodule.span ℂ (Set.range (gmon (m := m) X))
  have hs (s : κ) : ∀ f ∈ S, Adm (X s) l f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨α, rfl⟩ := hf
      rw [gmon_succ]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add f g hf hg ihf ihg => simpa using S.add_mem ihf ihg
    | smul z f hf ih => simpa using S.smul_mem z ih
  have hc' : ∀ f ∈ S, Adm c l f ∈ S := by
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨s, rfl⟩ := hc
      exact hs s
    | zero =>
      intro f hf
      simp [Adm]
    | add c d hc hd ihc ihd =>
      intro f hf
      rw [Adm_vec_add, LinearMap.add_apply]
      exact S.add_mem (ihc f hf) (ihd f hf)
    | smul z c hc ih =>
      intro f hf
      rw [Adm_vec_smul, LinearMap.smul_apply]
      exact S.smul_mem _ (ih f hf)
  exact hc' f hf

/-- If the standard basis of `ℚ³` lies in the `ℚ`-span of the slot vectors,
then the slot monomials span all of `FA3 m`. -/
theorem single_mem_span_gmon {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : κ → Fin 3 → ℚ)
    (hX : ∀ t : Fin 3, (Pi.single t 1 : Fin 3 → ℚ) ∈
      Submodule.span ℚ (Set.range X))
    (i : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    Finsupp.single i (1 : ℂ) ∈
      Submodule.span ℂ (Set.range (gmon (m := m) X)) := by
  classical
  let S := Submodule.span ℂ (Set.range (gmon (m := m) X))
  have hbuild : ∀ α : Fin 3 → Fin m → ℕ,
      Finsupp.single (α 0, α 1, α 2) (1 : ℂ) ∈ S := by
    intro α
    induction α using exp_induction with
    | hzero =>
      apply Submodule.subset_span
      refine ⟨0, ?_⟩
      rw [gmon_zero]
      rfl
    | hstep α t l ih =>
      have hc := gmon_span_stable X (Pi.single t 1) (hX t) l _ ih
      fin_cases t
      · have hc' : (Real.sqrt ((α 0 l : ℝ) + 1) : ℂ) •
            Finsupp.single (Function.update (α 0) l (α 0 l + 1), α 1, α 2) 1 ∈ S := by
          simpa [Adm, Pi.single_apply, copy1, adF, Finsupp.lsum_single,
            Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using hc
        have hn : (Real.sqrt ((α 0 l : ℝ) + 1) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
        have hh := S.smul_mem (Real.sqrt ((α 0 l : ℝ) + 1) : ℂ)⁻¹ hc'
        simpa [smul_smul, hn, bump] using hh
      · have hc' : (Real.sqrt ((α 1 l : ℝ) + 1) : ℂ) •
            Finsupp.single (α 0, Function.update (α 1) l (α 1 l + 1), α 2) 1 ∈ S := by
          simpa [Adm, Pi.single_apply, copy2, adF, Finsupp.lsum_single,
            Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using hc
        have hn : (Real.sqrt ((α 1 l : ℝ) + 1) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
        have hh := S.smul_mem (Real.sqrt ((α 1 l : ℝ) + 1) : ℂ)⁻¹ hc'
        simpa [smul_smul, hn, bump] using hh
      · have hc' : (Real.sqrt ((α 2 l : ℝ) + 1) : ℂ) •
            Finsupp.single (α 0, α 1, Function.update (α 2) l (α 2 l + 1)) 1 ∈ S := by
          simpa [Adm, Pi.single_apply, copy3, adF, Finsupp.lsum_single,
            Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using hc
        have hn : (Real.sqrt ((α 2 l : ℝ) + 1) : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
        have hh := S.smul_mem (Real.sqrt ((α 2 l : ℝ) + 1) : ℂ)⁻¹ hc'
        simpa [smul_smul, hn, bump] using hh
  simpa using hbuild (![i.1, i.2.1, i.2.2] : Fin 3 → Fin m → ℕ)

/-! ### Combination-mode number operators -/

/-- The number operator of the combination mode `c` (summed over modes),
*unnormalised*: its eigenvalue on a monomial with `k` factors of a slot `s`
with `⟨c, X s⟩ = ⟨c, c⟩` and all other used slots orthogonal to `c` is
`⟨c, c⟩ · k`. -/
noncomputable def Mnum (c : Fin 3 → ℚ) : FA3 m →ₗ[ℂ] FA3 m :=
  ∑ l, Adm c l ∘ₗ Am c l

theorem Mnum_gmon {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : κ → Fin 3 → ℚ) (α : κ → Fin m → ℕ) (s₀ : κ)
    (horth : ∀ t, t ≠ s₀ → α t ≠ 0 → pairQ (X s₀) (X t) = 0) :
    Mnum (X s₀) (gmon (m := m) X α) =
      ((pairQ (X s₀) (X s₀) * (degB (α s₀) : ℚ) : ℚ) : ℂ) • gmon X α := by
  classical
  simp only [Mnum, LinearMap.sum_apply, LinearMap.comp_apply]
  calc
    _ = ∑ l, ((α s₀ l : ℂ) * (pairQ (X s₀) (X s₀) : ℂ)) • gmon X α := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Am_gmon X α s₀ horth l, map_smul]
      by_cases hz : α s₀ l = 0
      · simp [hz]
      · rw [gmon_succ, bump_debump α s₀ l hz]
        simp
    _ = _ := by
      rw [← Finset.sum_smul]
      congr 1
      simp [degB, Finset.mul_sum, mul_comm]

theorem conservesDeg3_Mnum (c : Fin 3 → ℚ) :
    ConservesDeg3 (Mnum (m := m) c) := by
  classical
  intro p q hq
  by_contra hn
  have hz : (Mnum c (Finsupp.single p 1)) q = 0 := by
    simp only [Mnum, LinearMap.sum_apply, Finsupp.finsetSum_apply,
      LinearMap.comp_apply]
    apply Finset.sum_eq_zero
    intro l hl
    by_contra he
    obtain ⟨r, hr, hd⟩ := support_image_degree (Adm c l) 0 1
      (by simpa using shift_Adm c l) (Am c l (Finsupp.single p 1)) q
      (Finsupp.mem_support_iff.mpr he)
    have ha := shift_Am c l p r hr
    exact hn (by omega)
  exact Finsupp.mem_support_iff.mp hq hz

/-! ### Frames for the three pairs of copies

Pair labels: `a = 0 ↔ (copies 1,2)`, `a = 1 ↔ (copies 1,3)`,
`a = 2 ↔ (copies 2,3)`. All vectors have integer entries. `Bosons/CoherentBlocks.lean` normalizes their
creation monomials on each particle-number block. -/

/-- Centre-of-mass direction `v = (1,1,1)` in the proof of Lemma 6.6.
Its complex span is the manuscript's `V`. -/
def vVec : Fin 3 → ℚ := ![1, 1, 1]

/-- Retained directions in the manuscript's complement `W = Vᗮ`,
orthogonal to both `vVec` and `uVec a`. After division by `√6`, these
are the manuscript vectors `w₁₂`, `w₁₃`, and `w₂₃` from Lemma 6.6. We use
their unnormalized rational coordinates for the creation-operator calculations. -/
def wVec : Fin 3 → Fin 3 → ℚ := ![![1, 1, -2], ![1, -2, 1], ![-2, 1, 1]]

/-- Lost (difference) directions `e_a - e_b` for the three pairs. -/
def uVec : Fin 3 → Fin 3 → ℚ := ![![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

/-- The `a`-th frame: slot 0 ↦ centre of mass, slot 1 ↦ retained in-plane
direction, slot 2 ↦ lost difference direction. -/
def frame (a : Fin 3) : Fin 3 → Fin 3 → ℚ := ![vVec, wVec a, uVec a]

@[simp] lemma pairQ_v_v : pairQ vVec vVec = 3 := by
  norm_num [pairQ, vVec, Fin.sum_univ_three]
@[simp] lemma pairQ_w_w_same (a : Fin 3) : pairQ (wVec a) (wVec a) = 6 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
@[simp] lemma pairQ_u_u_same (a : Fin 3) : pairQ (uVec a) (uVec a) = 2 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
@[simp] lemma pairQ_v_w (a : Fin 3) : pairQ vVec (wVec a) = 0 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
@[simp] lemma pairQ_w_v (a : Fin 3) : pairQ (wVec a) vVec = 0 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
@[simp] lemma pairQ_v_u (a : Fin 3) : pairQ vVec (uVec a) = 0 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
@[simp] lemma pairQ_u_v (a : Fin 3) : pairQ (uVec a) vVec = 0 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
@[simp] lemma pairQ_w_u_same (a : Fin 3) : pairQ (wVec a) (uVec a) = 0 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
@[simp] lemma pairQ_u_w_same (a : Fin 3) : pairQ (uVec a) (wVec a) = 0 := by
  fin_cases a <;> norm_num [pairQ, vVec, wVec, uVec, Fin.sum_univ_three]
lemma pairQ_w_w_ne {a b : Fin 3} (h : a ≠ b) : pairQ (wVec a) (wVec b) = -3 := by
  fin_cases a <;> fin_cases b <;> first | exact (h rfl).elim | norm_num [pairQ, wVec, Fin.sum_univ_three]

/-- Each frame is an orthogonal basis direction set. -/
lemma frame_orth (a : Fin 3) :
    ∀ s t : Fin 3, s ≠ t → pairQ (frame a s) (frame a t) = 0 := by
  intro s t hst
  fin_cases a <;> fin_cases s <;> fin_cases t <;> first | exact (hst rfl).elim | norm_num [pairQ, frame, vVec, wVec, uVec, Fin.sum_univ_three]

/-- Each frame `ℚ`-spans the copy space. -/
lemma frame_spans (a : Fin 3) (t : Fin 3) :
    (Pi.single t 1 : Fin 3 → ℚ) ∈ Submodule.span ℚ (Set.range (frame a)) := by
  classical
  let coeff : Fin 3 → ℚ := fun s => frame a s t / (![3, 6, 2] : Fin 3 → ℚ) s
  have h : (∑ s, coeff s • frame a s) ∈
      Submodule.span ℚ (Set.range (frame a)) := by
    apply Submodule.sum_mem
    intro s hs
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  convert h using 1
  ext j
  fin_cases a <;> fin_cases t <;> fin_cases j <;>
    norm_num [coeff, frame, vVec, wVec, uVec, Fin.sum_univ_three, Pi.single_apply]

/-- The three difference-number operators (unnormalised: eigenvalues `2k`). -/
noncomputable def MopB (a : Fin 3) : FA3 m →ₗ[ℂ] FA3 m := Mnum (uVec a)

theorem conservesDeg3_MopB (a : Fin 3) : ConservesDeg3 (MopB (m := m) a) :=
  conservesDeg3_Mnum _

end GaussianTesting
