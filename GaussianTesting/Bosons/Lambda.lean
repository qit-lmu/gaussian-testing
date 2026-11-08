module

/-
The bosonic Gaussianity operator `Λ`, its kernel projection `P₀`, and the spectral
input for the concrete mean-zero bound in Theorem 6.4.

**Architecture.** The mode algebra lives on finitely-supported coefficient functions
(`Finsupp`), where creation/annihilation are *purely algebraic* linear maps (no
boundedness, all sums finite):

    a_l |n⟩ = √(n_l) |n − e_l⟩,   a†_l |n⟩ = √(n_l + 1) |n + e_l⟩.

CCR and the two/three-copy rotation generators

    Λ   = i Σ_l (a_l ⊗ a†_l − a†_l ⊗ a_l)                    (two copies)
    K_ab = i Σ_l (a_{l,a} a†_{l,b} − a†_{l,a} a_{l,b})        (three copies)

with the cyclic commutators `⁅K₁₂, K₂₃⁆ = i·(−K₁₃)` etc. — so `(K₁₂, K₂₃, −K₁₃)` is a
Hermitian angular-momentum triple on every finite total-number block, and the
finite-dimensional `kacT_gap` applies per block.

All these operators conserve total particle number, hence restrict to the finite
blocks; `P₀` and the three-copy `S` are then assembled as bounded block-diagonal
operators (`blockOp`). The same finite-core generator determines the graph
closure in `ClosedLambda.lean` and its physical realization in
`SchrodingerFockPair.lean`.
-/
public import GaussianTesting.Bosons.Fock
public import GaussianTesting.Kac.KacWalk

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {m : ℕ}

/-! ### A. Mode algebra on finitely-supported coefficients -/

/-- Single-copy algebraic Fock space: finitely-supported coefficient functions on
occupation vectors. -/
abbrev FA (m : ℕ) := (Fin m → ℕ) →₀ ℂ


/-- Annihilation `a_l`. -/
def aF (l : Fin m) : FA m →ₗ[ℂ] FA m :=
  Finsupp.lsum ℂ fun n =>
    (Real.sqrt (n l) : ℂ) • Finsupp.lsingle (Function.update n l (n l - 1))

/-- Creation `a†_l`. -/
def adF (l : Fin m) : FA m →ₗ[ℂ] FA m :=
  Finsupp.lsum ℂ fun n =>
    (Real.sqrt (n l + 1) : ℂ) • Finsupp.lsingle (Function.update n l (n l + 1))

/-- CCR, diagonal: `[a_l, a†_l] = 1`. -/
lemma ccr_same (l : Fin m) :
    aF l ∘ₗ adF l - adF l ∘ₗ aF l = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro n c
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply,
    aF, adF, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply,
    map_smul, Function.update_self, Function.update_idem]
  by_cases hn : n l = 0
  · simpa [hn] using congrArg (fun v => Finsupp.single v c) (show Function.update n l 0 = n by simp [hn])
  · have hpos : 0 < n l := Nat.pos_of_ne_zero hn
    have hu : Function.update n l (n l - 1 + 1) = n := by
      rw [Nat.sub_add_cancel hpos, Function.update_eq_self]
    have hs (k : ℕ) : (Real.sqrt (k : ℝ) : ℂ) * (Real.sqrt (k : ℝ) : ℂ) = k := by
      rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]
      rfl
    simp only [Nat.add_sub_cancel, Function.update_eq_self, hu, smul_smul]
    have hc : (↑(n l - 1) : ℝ) + 1 = (n l : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hpos
    rw [hc]
    have hs' := hs (n l + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hs'
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hs', hs]
    module

/-- CCR, off-diagonal: all generators with distinct mode indices commute, and
`[a_l, a_k] = [a†_l, a†_k] = 0`. -/
lemma ccr_ne {l k : Fin m} (hlk : l ≠ k) :
    aF l ∘ₗ adF k = adF k ∘ₗ aF l ∧ aF l ∘ₗ aF k = aF k ∘ₗ aF l ∧
      adF l ∘ₗ adF k = adF k ∘ₗ adF l := by
  classical
  have hkl := Ne.symm hlk
  constructor
  · apply Finsupp.lhom_ext
    intro n c
    simp [aF, adF, Function.update_of_ne hlk,
      Function.update_of_ne hkl, Function.update_comm hlk, mul_comm, mul_left_comm, mul_assoc]
  constructor
  · apply Finsupp.lhom_ext
    intro n c
    simp [aF, Function.update_of_ne hlk,
      Function.update_of_ne hkl, Function.update_comm hlk, mul_comm, mul_left_comm, mul_assoc]
  · apply Finsupp.lhom_ext
    intro n c
    simp [adF, Function.update_of_ne hlk,
      Function.update_of_ne hkl, Function.update_comm hlk, mul_comm, mul_left_comm, mul_assoc]

/-! ### B. Three copies and the rotation generators -/

/-- Three-copy algebraic space. -/
abbrev FA3 (m : ℕ) := ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) →₀ ℂ


/-- Apply a single-copy map on the first copy. -/
def copy1 (A : FA m →ₗ[ℂ] FA m) : FA3 m →ₗ[ℂ] FA3 m :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (Finsupp.lmapDomain ℂ ℂ (fun i => (i, p.2.1, p.2.2)) (A (Finsupp.single p.1 1)))

/-- Apply a single-copy map on the second copy. -/
def copy2 (A : FA m →ₗ[ℂ] FA m) : FA3 m →ₗ[ℂ] FA3 m :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (Finsupp.lmapDomain ℂ ℂ (fun i => (p.1, i, p.2.2)) (A (Finsupp.single p.2.1 1)))

/-- Apply a single-copy map on the third copy. -/
def copy3 (A : FA m →ₗ[ℂ] FA m) : FA3 m →ₗ[ℂ] FA3 m :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (Finsupp.lmapDomain ℂ ℂ (fun i => (p.1, p.2.1, i)) (A (Finsupp.single p.2.2 1)))

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

private lemma copy1_add (A B : FA m →ₗ[ℂ] FA m) :
    copy1 (A + B) = copy1 A + copy1 B := by
  apply basis_ext
  intro p
  simp only [copy1_single, LinearMap.add_apply, map_add, one_smul]

private lemma copy1_zero : copy1 (0 : FA m →ₗ[ℂ] FA m) = 0 := by
  apply basis_ext
  intro p
  simp only [copy1_single, LinearMap.zero_apply, map_zero, smul_zero]

private lemma copy2_add (A B : FA m →ₗ[ℂ] FA m) :
    copy2 (A + B) = copy2 A + copy2 B := by
  apply basis_ext
  intro p
  simp only [copy2_single, LinearMap.add_apply, map_add, one_smul]

private lemma copy2_zero : copy2 (0 : FA m →ₗ[ℂ] FA m) = 0 := by
  apply basis_ext
  intro p
  simp only [copy2_single, LinearMap.zero_apply, map_zero, smul_zero]

private lemma copy3_add (A B : FA m →ₗ[ℂ] FA m) :
    copy3 (A + B) = copy3 A + copy3 B := by
  apply basis_ext
  intro p
  simp only [copy3_single, LinearMap.add_apply, map_add, one_smul]

private lemma copy3_zero : copy3 (0 : FA m →ₗ[ℂ] FA m) = 0 := by
  apply basis_ext
  intro p
  simp only [copy3_single, LinearMap.zero_apply, map_zero, smul_zero]

private lemma middle_swapB {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a b c d : Module.End ℂ V) (h : b * c = c * b) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  simp only [mul_assoc]
  rw [← mul_assoc b c d, h, mul_assoc]

private def tt (A B C : Module.End ℂ (FA m)) : Module.End ℂ (FA3 m) :=
  copy1 A * copy2 B * copy3 C

private lemma tt_mul (A B C D E F : Module.End ℂ (FA m)) :
    tt A B C * tt D E F = tt (A * D) (B * E) (C * F) := by
  have h31 : copy3 C * copy1 D = copy1 D * copy3 C := (copy13_comm D C).symm
  have h32 : copy3 C * copy2 E = copy2 E * copy3 C := (copy23_comm E C).symm
  have h21 : copy2 B * copy1 D = copy1 D * copy2 B := (copy12_comm D B).symm
  have hc : copy3 C * (copy1 D * copy2 E) = (copy1 D * copy2 E) * copy3 C := by
    rw [← mul_assoc, h31, mul_assoc, h32, ← mul_assoc]
  unfold tt
  rw [middle_swapB _ _ _ _ hc, middle_swapB _ _ _ _ h21]
  rw [show copy1 A * copy1 D = copy1 (A * D) from copy1_comp A D,
    show copy2 B * copy2 E = copy2 (B * E) from copy2_comp B E,
    show copy3 C * copy3 F = copy3 (C * F) from copy3_comp C F]

private lemma copy1_neg (A : FA m →ₗ[ℂ] FA m) : copy1 (-A) = -copy1 A := by
  apply basis_ext
  intro p
  simp only [copy1_single, LinearMap.neg_apply, map_neg, one_smul]

private lemma copy2_neg (A : FA m →ₗ[ℂ] FA m) : copy2 (-A) = -copy2 A := by
  apply basis_ext
  intro p
  simp only [copy2_single, LinearMap.neg_apply, map_neg, one_smul]

private lemma copy3_neg (A : FA m →ₗ[ℂ] FA m) : copy3 (-A) = -copy3 A := by
  apply basis_ext
  intro p
  simp only [copy3_single, LinearMap.neg_apply, map_neg, one_smul]

private lemma tt_neg1 (A B C : Module.End ℂ (FA m)) :
    tt (-A) B C = -tt A B C := by
  unfold tt
  rw [copy1_neg]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Module.End.mul_apply]

private lemma tt_neg2 (A B C : Module.End ℂ (FA m)) :
    tt A (-B) C = -tt A B C := by
  unfold tt
  rw [copy2_neg]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Module.End.mul_apply]

private lemma tt_neg3 (A B C : Module.End ℂ (FA m)) :
    tt A B (-C) = -tt A B C := by
  unfold tt
  rw [copy3_neg]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Module.End.mul_apply]

private lemma tt_sub1 (A B C D : Module.End ℂ (FA m)) :
    tt (A - B) C D = tt A C D - tt B C D := by
  unfold tt
  rw [copy1_sub]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Module.End.mul_apply]
private lemma tt_sub2 (A B C D : Module.End ℂ (FA m)) :
    tt A (B - C) D = tt A B D - tt A C D := by
  unfold tt
  rw [copy2_sub]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Module.End.mul_apply, map_sub]
private lemma tt_sub3 (A B C D : Module.End ℂ (FA m)) :
    tt A B (C - D) = tt A B C - tt A B D := by
  unfold tt
  rw [copy3_sub]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Module.End.mul_apply, map_sub]
private lemma tt_zero1 (B C : Module.End ℂ (FA m)) : tt 0 B C = 0 := by
  simp [tt, copy1_zero]
private lemma tt_zero2 (A C : Module.End ℂ (FA m)) : tt A 0 C = 0 := by
  simp [tt, copy2_zero]
private lemma tt_zero3 (A B : Module.End ℂ (FA m)) : tt A B 0 = 0 := by
  simp [tt, copy3_zero]

private lemma tt_lie12 (A B C D : Module.End ℂ (FA m)) :
    ⁅tt A B 1, tt 1 C D⁆ = tt A ⁅B,C⁆ D := by
  simp only [Ring.lie_def, tt_mul, one_mul, mul_one, tt_sub2]
private lemma tt_lie23 (A B C D : Module.End ℂ (FA m)) :
    ⁅tt 1 A B, tt C 1 D⁆ = tt C A ⁅B,D⁆ := by
  simp only [Ring.lie_def, tt_mul, one_mul, mul_one, tt_sub3]
private lemma tt_lie31 (A B C D : Module.End ℂ (FA m)) :
    ⁅tt A 1 B, tt C D 1⁆ = tt ⁅A,C⁆ D B := by
  simp only [Ring.lie_def, tt_mul, one_mul, mul_one, tt_sub1]

private lemma mode_lie (l k : Fin m) :
    ⁅aF l, adF k⁆ = (if l = k then 1 else 0) ∧
    ⁅adF l, aF k⁆ = (if l = k then -1 else 0) ∧
    ⁅aF l, aF k⁆ = 0 ∧ ⁅adF l, adF k⁆ = 0 := by
  classical
  by_cases h : l = k
  · subst k
    have hc : ⁅aF l, adF l⁆ = 1 := ccr_same l
    simp only [ite_true]
    refine ⟨hc, ?_, ?_, ?_⟩
    · simp only [Ring.lie_def] at hc ⊢
      apply LinearMap.ext
      intro v
      apply Finsupp.ext
      intro q
      have hp := congrArg (fun T : Module.End ℂ (FA m) => T v q) hc
      simp only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.one_apply,
        Finsupp.sub_apply, Finsupp.neg_apply] at hp ⊢
      linear_combination -hp
    · simp only [Ring.lie_def, sub_self]
    · simp only [Ring.lie_def, sub_self]
  · have hc := ccr_ne h
    have hc' := ccr_ne (Ne.symm h)
    simp only [h, ite_false, Ring.lie_def, Module.End.mul_eq_comp,
      hc.1, hc.2.1, hc.2.2, hc'.1, sub_self, true_and]

private def X12 (l : Fin m) := tt (aF l) (adF l) 1 - tt (adF l) (aF l) 1
private def X23 (l : Fin m) := tt 1 (aF l) (adF l) - tt 1 (adF l) (aF l)
private def X13 (l : Fin m) := tt (aF l) 1 (adF l) - tt (adF l) 1 (aF l)

private lemma ring_sub_lieB (a b c : Module.End ℂ (FA3 m)) :
    ⁅a - b, c⁆ = ⁅a,c⁆ - ⁅b,c⁆ := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Ring.lie_def, Module.End.mul_apply, map_sub]
  all_goals ring
private lemma ring_lie_subB (a b c : Module.End ℂ (FA3 m)) :
    ⁅a, b-c⁆ = ⁅a,b⁆ - ⁅a,c⁆ := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Ring.lie_def, Module.End.mul_apply, map_sub]
  all_goals ring

private lemma Xcomm12 (l k : Fin m) :
    ⁅X12 l, X23 k⁆ = if l = k then -X13 l else 0 := by
  classical
  unfold X12 X23
  simp only [ring_sub_lieB (m := m), ring_lie_subB (m := m)]
  simp only [tt_lie12]
  rcases mode_lie l k with ⟨h1,h2,h3,h4⟩
  rw [h1,h2,h3,h4]
  split_ifs with h
  · subst k
    simp only [X13, tt_neg2, tt_zero2]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro q
    simp
    all_goals ring
  · simp only [tt_zero2]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro q
    simp

private lemma Xcomm23 (l k : Fin m) :
    ⁅X23 l, X13 k⁆ = if l = k then -X12 l else 0 := by
  classical
  unfold X23 X13
  simp only [ring_sub_lieB (m := m), ring_lie_subB (m := m)]
  simp only [tt_lie23]
  rcases mode_lie l k with ⟨h1,h2,h3,h4⟩
  rw [h1,h2,h3,h4]
  split_ifs with h
  · subst k
    simp only [X12, tt_neg3, tt_zero3]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro q
    simp
  · simp only [tt_zero3]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro q
    simp

private lemma Xcomm31 (l k : Fin m) :
    ⁅X13 l, X12 k⁆ = if l = k then -X23 l else 0 := by
  classical
  unfold X13 X12
  simp only [ring_sub_lieB (m := m), ring_lie_subB (m := m)]
  simp only [tt_lie31]
  rcases mode_lie l k with ⟨h1,h2,h3,h4⟩
  rw [h1,h2,h3,h4]
  split_ifs with h
  · subst k
    simp only [X23, tt_neg1, tt_zero1]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro q
    simp
    all_goals ring
  · simp only [tt_zero1]
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro q
    simp

/-- The rotation generator between copies 1 and 2:
`K₁₂ = i Σ_l (a_{l,1} a†_{l,2} − a†_{l,1} a_{l,2})`. -/
def K12 (m : ℕ) : FA3 m →ₗ[ℂ] FA3 m :=
  Complex.I • ∑ l : Fin m,
    (copy1 (aF l) ∘ₗ copy2 (adF l) - copy1 (adF l) ∘ₗ copy2 (aF l))

/-- `K₂₃`. -/
def K23 (m : ℕ) : FA3 m →ₗ[ℂ] FA3 m :=
  Complex.I • ∑ l : Fin m,
    (copy2 (aF l) ∘ₗ copy3 (adF l) - copy2 (adF l) ∘ₗ copy3 (aF l))

/-- `K₁₃`. -/
def K13 (m : ℕ) : FA3 m →ₗ[ℂ] FA3 m :=
  Complex.I • ∑ l : Fin m,
    (copy1 (aF l) ∘ₗ copy3 (adF l) - copy1 (adF l) ∘ₗ copy3 (aF l))

private lemma K12_form : K12 m = Complex.I • ∑ l : Fin m, X12 l := by
  unfold K12 X12 tt
  simp only [show (1 : Module.End ℂ (FA m)) = LinearMap.id from rfl,
    copy3_id, Module.End.mul_eq_comp,
    LinearMap.comp_id]

private lemma K23_form : K23 m = Complex.I • ∑ l : Fin m, X23 l := by
  unfold K23 X23 tt
  simp only [show (1 : Module.End ℂ (FA m)) = LinearMap.id from rfl,
    copy1_id, Module.End.mul_eq_comp,
    LinearMap.id_comp]

private lemma K13_form : K13 m = Complex.I • ∑ l : Fin m, X13 l := by
  unfold K13 X13 tt
  simp only [show (1 : Module.End ℂ (FA m)) = LinearMap.id from rfl,
    copy2_id, Module.End.mul_eq_comp,
    LinearMap.comp_id]

private lemma bracket_smulB (c d : ℂ) (A B : Module.End ℂ (FA3 m)) :
    ⁅c • A, d • B⁆ = (c*d) • ⁅A,B⁆ := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Ring.lie_def, Module.End.mul_apply]
  all_goals ring

private lemma bracket_sumB {ι : Type*} [Fintype ι]
    (A B : ι → Module.End ℂ (FA3 m)) :
    ⁅∑ i, A i, ∑ j, B j⁆ = ∑ i, ∑ j, ⁅A i, B j⁆ := by
  apply LinearMap.ext
  intro v
  simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, map_sum, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

private lemma bracket_neg_leftB (A B : Module.End ℂ (FA3 m)) :
    ⁅-A,B⁆ = -⁅A,B⁆ := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Ring.lie_def, Module.End.mul_apply]
  all_goals ring
private lemma bracket_neg_rightB (A B : Module.End ℂ (FA3 m)) :
    ⁅A,-B⁆ = -⁅A,B⁆ := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [Ring.lie_def, Module.End.mul_apply]
  all_goals ring

/-- The cyclic su(2) relations for `(Jx, Jy, Jz) := (K₁₂, K₂₃, −K₁₃)`:
`⁅K₁₂, K₂₃⁆ = i • (−K₁₃)` (and cyclically). Derived from the CCR via the gl-relations
`[E_ab, E_cd] = δ_bc E_ad − δ_ad E_cb`. -/
lemma commutator_K12_K23 (m : ℕ) : ⁅K12 m, K23 m⁆ = Complex.I • (-K13 m) := by
  classical
  simp only [K12_form, K23_form, K13_form,
    bracket_smulB (m := m), bracket_sumB (m := m), Xcomm12]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [smul_smul, Complex.I_mul_I, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    Finset.sum_neg_distrib]



lemma commutator_K23_negK13 (m : ℕ) : ⁅K23 m, -K13 m⁆ = Complex.I • K12 m := by
  classical
  simp only [K12_form, K23_form, K13_form, bracket_neg_rightB (m := m),
    bracket_smulB (m := m), bracket_sumB (m := m), Xcomm23]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [smul_smul, Complex.I_mul_I, LinearMap.sum_apply,
    Finset.sum_neg_distrib]



lemma commutator_negK13_K12 (m : ℕ) : ⁅-K13 m, K12 m⁆ = Complex.I • K23 m := by
  classical
  simp only [K12_form, K23_form, K13_form, bracket_neg_leftB (m := m),
    bracket_smulB (m := m), bracket_sumB (m := m), Xcomm31]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  simp [smul_smul, Complex.I_mul_I, LinearMap.sum_apply,
    Finset.sum_neg_distrib]



/-! ### C. Degree conservation and block restriction -/

/-- Three-copy total particle number. -/
def degB3 {m : ℕ} (p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) : ℕ :=
  degB p.1 + degB p.2.1 + degB p.2.2

instance degB3_fiber_fintype (m n : ℕ) :
    Fintype {p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ) // degB3 p = n} := by
  classical
  have hle (p : {p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ) //
      degB3 p = n}) (j : Fin m) :
      p.1.1 j ≤ n ∧ p.1.2.1 j ≤ n ∧ p.1.2.2 j ≤ n := by
    have h1 : p.1.1 j ≤ degB p.1.1 := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    have h2 : p.1.2.1 j ≤ degB p.1.2.1 := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    have h3 : p.1.2.2 j ≤ degB p.1.2.2 := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    have hp := p.2
    unfold degB3 at hp
    omega
  exact Fintype.ofInjective
    (f := fun p : {p : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ) // degB3 p = n} =>
      ((fun j => (⟨p.1.1 j, Nat.lt_succ_of_le (hle p j).1⟩ : Fin (n + 1))),
       (fun j => (⟨p.1.2.1 j, Nat.lt_succ_of_le (hle p j).2.1⟩ : Fin (n + 1))),
       (fun j => (⟨p.1.2.2 j, Nat.lt_succ_of_le (hle p j).2.2⟩ : Fin (n + 1)))))
    (by
      intro p q h
      apply Subtype.ext
      have h1 := congrArg Prod.fst h
      have h2 := congrArg (fun x => x.2.1) h
      have h3 := congrArg (fun x => x.2.2) h
      apply Prod.ext
      · funext j
        exact congrArg Fin.val (congrFun h1 j)
      · apply Prod.ext
        · funext j
          exact congrArg Fin.val (congrFun h2 j)
        · funext j
          exact congrArg Fin.val (congrFun h3 j))

/-- A `Finsupp` endomorphism conserves degree if the image of every basis vector is
supported on its degree fiber. -/
def ConservesDeg3 (T : FA3 m →ₗ[ℂ] FA3 m) : Prop :=
  ∀ p q, q ∈ (T (Finsupp.single p 1)).support → degB3 q = degB3 p

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

private lemma conserves_smul {T : FA3 m →ₗ[ℂ] FA3 m}
    (hT : ConservesDeg3 T) (c : ℂ) : ConservesDeg3 (c • T) := by
  intro p q h
  exact hT p q (Finsupp.support_smul h)

private lemma conserves_sub {S T : FA3 m →ₗ[ℂ] FA3 m}
    (hS : ConservesDeg3 S) (hT : ConservesDeg3 T) : ConservesDeg3 (S - T) := by
  intro p q h
  rcases Finset.mem_union.mp (Finsupp.support_sub h) with h | h
  · exact hS p q h
  · exact hT p q h

private lemma conserves_sum {ι : Type*} (s : Finset ι) (T : ι → FA3 m →ₗ[ℂ] FA3 m)
    (hT : ∀ i ∈ s, ConservesDeg3 (T i)) : ConservesDeg3 (∑ i ∈ s, T i) := by
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
    ConservesDeg3 (copy1 (aF l) ∘ₗ copy2 (adF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copy1, copy2, aF, adF,
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
  have h2 := degB_update p.2.1 l (p.2.1 l + 1)
  dsimp [degB3]
  omega

private lemma conserve12r (l : Fin m) :
    ConservesDeg3 (copy1 (adF l) ∘ₗ copy2 (aF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copy1, copy2, aF, adF,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.lmapDomain_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.2.1 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have h1 := degB_update p.1 l (p.1 l + 1)
  have h2 := degB_update p.2.1 l (p.2.1 l - 1)
  dsimp [degB3]
  omega

private lemma conserve23f (l : Fin m) :
    ConservesDeg3 (copy2 (aF l) ∘ₗ copy3 (adF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copy2, copy3, aF, adF,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.lmapDomain_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.2.1 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have h1 := degB_update p.2.1 l (p.2.1 l - 1)
  have h2 := degB_update p.2.2 l (p.2.2 l + 1)
  dsimp [degB3]
  omega

private lemma conserve23r (l : Fin m) :
    ConservesDeg3 (copy2 (adF l) ∘ₗ copy3 (aF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copy2, copy3, aF, adF,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.lmapDomain_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.2.2 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have h1 := degB_update p.2.1 l (p.2.1 l + 1)
  have h2 := degB_update p.2.2 l (p.2.2 l - 1)
  dsimp [degB3]
  omega

private lemma conserve13f (l : Fin m) :
    ConservesDeg3 (copy1 (aF l) ∘ₗ copy3 (adF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copy1, copy3, aF, adF,
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
  have h2 := degB_update p.2.2 l (p.2.2 l + 1)
  dsimp [degB3]
  omega

private lemma conserve13r (l : Fin m) :
    ConservesDeg3 (copy1 (adF l) ∘ₗ copy3 (aF l)) := by
  classical
  intro p q h
  simp only [LinearMap.comp_apply, copy1, copy3, aF, adF,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.lmapDomain_apply,
    LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.mapDomain_single, one_smul, Finsupp.smul_single,
    smul_eq_mul, mul_one] at h
  obtain ⟨hq, hc⟩ := (Finsupp.mem_support_single _ _ _).mp h
  subst q
  have hp : p.2.2 l ≠ 0 := by
    intro hz
    simp [hz] at hc
  have h1 := degB_update p.1 l (p.1 l + 1)
  have h2 := degB_update p.2.2 l (p.2.2 l - 1)
  dsimp [degB3]
  omega

lemma conservesDeg3_K12 (m : ℕ) : ConservesDeg3 (K12 m) := by
  apply conserves_smul
  apply conserves_sum
  intro l _
  exact conserves_sub (conserve12f l) (conserve12r l)

lemma conservesDeg3_K23 (m : ℕ) : ConservesDeg3 (K23 m) := by
  apply conserves_smul
  apply conserves_sum
  intro l _
  exact conserves_sub (conserve23f l) (conserve23r l)

lemma conservesDeg3_K13 (m : ℕ) : ConservesDeg3 (K13 m) := by
  apply conserves_smul
  apply conserves_sum
  intro l _
  exact conserves_sub (conserve13f l) (conserve13r l)

def blockLift3 (n : ℕ) : BlockSp (degB3 (m := m)) n →ₗ[ℂ] FA3 m where
  toFun v := ∑ p, v p • Finsupp.single p.1 1
  map_add' v w := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PiLp.smul_apply, smul_smul, smul_eq_mul, Finset.smul_sum, RingHom.id_apply]

private lemma blockLift3_apply (n : ℕ) (v : BlockSp (degB3 (m := m)) n)
    (q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    blockLift3 n v q = if h : degB3 q = n then v ⟨q, h⟩ else 0 := by
  classical
  simp only [blockLift3, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : degB3 q = n
  · rw [dite_eq_left h, Finset.sum_eq_single (⟨q, h⟩ : {q // degB3 q = n})]
    · simp
    · intro p _ hp
      exact ite_eq_right (fun he => hp (Subtype.ext he))
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro p _
    exact ite_eq_right (fun (hp : p.1 = q) => h (hp ▸ p.2))

/-- Restriction of a degree-conserving algebraic endomorphism to the finite block of
degree `n`, as a linear map on `BlockSp degB3 n`. -/
def toBlock3 (T : FA3 m →ₗ[ℂ] FA3 m) (n : ℕ) :
    BlockSp (degB3 (m := m)) n →ₗ[ℂ] BlockSp (degB3 (m := m)) n := by
  exact
    { toFun := fun v => WithLp.toLp 2 fun q => T (blockLift3 n v) q.1
      map_add' := by
        intro v w
        ext q
        simp [map_add]
      map_smul' := by
        intro c v
        ext q
        simp [map_smul] }

private lemma blockLift3_toBlock3 {T : FA3 m →ₗ[ℂ] FA3 m}
    (hT : ConservesDeg3 T) (n : ℕ) (v : BlockSp (degB3 (m := m)) n) :
    blockLift3 n (toBlock3 T n v) = T (blockLift3 n v) := by
  classical
  ext q
  rw [blockLift3_apply]
  split_ifs with hq
  · rfl
  · symm
    change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) q = 0
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply]
    apply Finset.sum_eq_zero
    intro p _
    have hz : (T (Finsupp.single p.1 1)) q = 0 := by
      by_contra h
      exact hq ((hT p.1 q (Finsupp.mem_support_iff.mpr h)).trans p.2)
    rw [hz, smul_zero]

/-- Restriction respects composition for degree-conserving maps. -/
lemma toBlock3_comp {S T : FA3 m →ₗ[ℂ] FA3 m} (_hS : ConservesDeg3 S)
    (hT : ConservesDeg3 T) (n : ℕ) :
    toBlock3 (S ∘ₗ T) n = toBlock3 S n ∘ₗ toBlock3 T n := by
  apply LinearMap.ext
  intro v
  ext q
  change (S (T (blockLift3 n v))) q.1 =
    (S (blockLift3 n (toBlock3 T n v))) q.1
  rw [blockLift3_toBlock3 hT]


lemma toBlock3_apply (T : FA3 m →ₗ[ℂ] FA3 m) (n : ℕ)
    (v : BlockSp (degB3 (m := m)) n) (q : {q // degB3 q = n}) :
    toBlock3 T n v q = ∑ p : {p // degB3 p = n}, v p * (T (Finsupp.single p.1 1)) q.1 := by
  classical
  change (T (∑ p : {p // degB3 p = n}, v p • Finsupp.single p.1 1)) q.1 = _
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

lemma toBlock3_symmetric (T : FA3 m →ₗ[ℂ] FA3 m)
    (h : ∀ p q, (T (Finsupp.single p 1)) q = star ((T (Finsupp.single q 1)) p))
    (n : ℕ) : (toBlock3 T n).IsSymmetric := by
  classical
  intro v w
  simp only [PiLp.inner_apply, RCLike.inner_apply, toBlock3_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [h]
  simp
  all_goals ring

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

private lemma pair_entry12f (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy1 (aF l) ∘ₗ copy2 (adF l)) (Finsupp.single p 1)) q =
      ((aF l (Finsupp.single p.1 1)) q.1) * ((adF l (Finsupp.single p.2.1 1)) q.2.1) * ((Finsupp.single p.2.2 (1 : ℂ)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, copy2, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

private lemma pair_entry12r (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy1 (adF l) ∘ₗ copy2 (aF l)) (Finsupp.single p 1)) q =
      ((adF l (Finsupp.single p.1 1)) q.1) * ((aF l (Finsupp.single p.2.1 1)) q.2.1) * ((Finsupp.single p.2.2 (1 : ℂ)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, copy2, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

private lemma pair_entry23f (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy2 (aF l) ∘ₗ copy3 (adF l)) (Finsupp.single p 1)) q =
      ((Finsupp.single p.1 (1 : ℂ)) q.1) * ((aF l (Finsupp.single p.2.1 1)) q.2.1) * ((adF l (Finsupp.single p.2.2 1)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy2, copy3, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

private lemma pair_entry23r (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy2 (adF l) ∘ₗ copy3 (aF l)) (Finsupp.single p 1)) q =
      ((Finsupp.single p.1 (1 : ℂ)) q.1) * ((adF l (Finsupp.single p.2.1 1)) q.2.1) * ((aF l (Finsupp.single p.2.2 1)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy2, copy3, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

private lemma pair_entry13f (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy1 (aF l) ∘ₗ copy3 (adF l)) (Finsupp.single p 1)) q =
      ((aF l (Finsupp.single p.1 1)) q.1) * ((Finsupp.single p.2.1 (1 : ℂ)) q.2.1) * ((adF l (Finsupp.single p.2.2 1)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, copy3, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

private lemma pair_entry13r (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy1 (adF l) ∘ₗ copy3 (aF l)) (Finsupp.single p 1)) q =
      ((adF l (Finsupp.single p.1 1)) q.1) * ((Finsupp.single p.2.1 (1 : ℂ)) q.2.1) * ((aF l (Finsupp.single p.2.2 1)) q.2.2) := by
  classical
  rcases p with ⟨p1,p2,p3⟩
  rcases q with ⟨q1,q2,q3⟩
  simp [copy1, copy3, aF, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all
  ring

private lemma single_entry_symm {ι : Type*} [DecidableEq ι] (p q : ι) :
    (Finsupp.single p (1 : ℂ)) q = star ((Finsupp.single q (1 : ℂ)) p) := by
  simp [Finsupp.single_apply, eq_comm]

private lemma pair_adj12 (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy1 (aF l) ∘ₗ copy2 (adF l)) (Finsupp.single p 1)) q =
      star (((copy1 (adF l) ∘ₗ copy2 (aF l)) (Finsupp.single q 1)) p) := by
  rw [pair_entry12f, pair_entry12r]
  rw [aF_entry l p.1 q.1, adF_entry l p.2.1 q.2.1, single_entry_symm p.2.2 q.2.2]
  simp only [star_mul]
  ring

private lemma K12_entry (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (K12 m (Finsupp.single p 1)) q = star ((K12 m (Finsupp.single q 1)) p) := by
  classical
  simp only [K12, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
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

private lemma pair_adj23 (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy2 (aF l) ∘ₗ copy3 (adF l)) (Finsupp.single p 1)) q =
      star (((copy2 (adF l) ∘ₗ copy3 (aF l)) (Finsupp.single q 1)) p) := by
  rw [pair_entry23f, pair_entry23r]
  rw [aF_entry l p.2.1 q.2.1, adF_entry l p.2.2 q.2.2, single_entry_symm p.1 q.1]
  simp only [star_mul]
  ring

private lemma K23_entry (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (K23 m (Finsupp.single p 1)) q = star ((K23 m (Finsupp.single q 1)) p) := by
  classical
  simp only [K23, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.sub_apply, smul_eq_mul,
    star_mul, star_sum, Complex.star_def, Complex.conj_I, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hf := pair_adj23 l p q
  have hr := congrArg star (pair_adj23 l q p)
  simp only [star_star] at hr
  rw [hf, ← hr]
  simp only [Complex.star_def, map_sub]
  ring

private lemma pair_adj13 (l : Fin m)
    (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    ((copy1 (aF l) ∘ₗ copy3 (adF l)) (Finsupp.single p 1)) q =
      star (((copy1 (adF l) ∘ₗ copy3 (aF l)) (Finsupp.single q 1)) p) := by
  rw [pair_entry13f, pair_entry13r]
  rw [aF_entry l p.1 q.1, adF_entry l p.2.2 q.2.2, single_entry_symm p.2.1 q.2.1]
  simp only [star_mul]
  ring

private lemma K13_entry (p q : (Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ)) :
    (K13 m (Finsupp.single p 1)) q = star ((K13 m (Finsupp.single q 1)) p) := by
  classical
  simp only [K13, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.sub_apply, smul_eq_mul,
    star_mul, star_sum, Complex.star_def, Complex.conj_I, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hf := pair_adj13 l p q
  have hr := congrArg star (pair_adj13 l q p)
  simp only [star_star] at hr
  rw [hf, ← hr]
  simp only [Complex.star_def, map_sub]
  ring

/-- The block restrictions of the `K`'s are symmetric (the generators are Hermitian:
their matrices have real entries and `K = i(X − Xᵀ)` shape). -/
lemma toBlock3_K12_isSymmetric (m n : ℕ) : (toBlock3 (K12 m) n).IsSymmetric := by
  exact toBlock3_symmetric (K12 m) K12_entry n

lemma toBlock3_K23_isSymmetric (m n : ℕ) : (toBlock3 (K23 m) n).IsSymmetric := by
  exact toBlock3_symmetric (K23 m) K23_entry n

lemma toBlock3_K13_isSymmetric (m n : ℕ) : (toBlock3 (K13 m) n).IsSymmetric := by
  exact toBlock3_symmetric (K13 m) K13_entry n

private lemma toBlock3_neg (T : FA3 m →ₗ[ℂ] FA3 m) (n : ℕ) :
    toBlock3 (-T) n = -toBlock3 T n := by
  apply LinearMap.ext
  intro v
  ext q
  rfl
private lemma toBlock3_sub (S T : FA3 m →ₗ[ℂ] FA3 m) (n : ℕ) :
    toBlock3 (S-T) n = toBlock3 S n - toBlock3 T n := by
  apply LinearMap.ext
  intro v
  ext q
  rfl
private lemma toBlock3_smul (c : ℂ) (T : FA3 m →ₗ[ℂ] FA3 m) (n : ℕ) :
    toBlock3 (c • T) n = c • toBlock3 T n := by
  apply LinearMap.ext
  intro v
  ext q
  rfl

private lemma conserves_neg {T : FA3 m →ₗ[ℂ] FA3 m} (h : ConservesDeg3 T) :
    ConservesDeg3 (-T) := by
  intro p q hq
  apply h p q
  simpa only [LinearMap.neg_apply, Finsupp.support_neg] using hq

private lemma toBlock3_lie {S T : FA3 m →ₗ[ℂ] FA3 m}
    (hS : ConservesDeg3 S) (hT : ConservesDeg3 T) (n : ℕ) :
    toBlock3 ⁅S,T⁆ n = ⁅toBlock3 S n, toBlock3 T n⁆ := by
  simp only [Ring.lie_def, Module.End.mul_eq_comp, toBlock3_sub,
    toBlock3_comp hS hT, toBlock3_comp hT hS]

/-- The per-block angular-momentum triple feeding the finite-dimensional Kac theorem. -/
def blockTriple (m n : ℕ) : AngularMomentum (BlockSp (degB3 (m := m)) n) where
  Jx := toBlock3 (K12 m) n
  Jy := toBlock3 (K23 m) n
  Jz := toBlock3 (-K13 m) n
  hJx := toBlock3_K12_isSymmetric m n
  hJy := toBlock3_K23_isSymmetric m n
  hJz := by
    rw [toBlock3_neg]
    intro v w
    change inner ℂ (-(toBlock3 (K13 m) n v)) w =
      inner ℂ v (-(toBlock3 (K13 m) n w))
    rw [inner_neg_left, inner_neg_right, toBlock3_K13_isSymmetric m n]
  comm_xy := by
    rw [← toBlock3_lie (conservesDeg3_K12 m) (conservesDeg3_K23 m) n, commutator_K12_K23, toBlock3_smul]
  comm_yz := by
    rw [← toBlock3_lie (conservesDeg3_K23 m) (conserves_neg (conservesDeg3_K13 m)) n, commutator_K23_negK13, toBlock3_smul]
  comm_zx := by
    rw [← toBlock3_lie (conserves_neg (conservesDeg3_K13 m)) (conservesDeg3_K12 m) n, commutator_negK13_K12, toBlock3_smul]

end

end GaussianTesting
