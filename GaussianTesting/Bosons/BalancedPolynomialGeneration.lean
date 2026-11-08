/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GaussianTesting.Bosons.BalancedQuadratic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dual.Lemmas

import Mathlib.Tactic

/-!
# Generation of balanced symmetric polynomials by quadratic invariants

The proof uses the elementary quadratic-lowering joint-kernel calculation.
Finite Fischer duality identifies a functional annihilating the quadratic
generators with a polynomial in that joint kernel; induction on balanced
degree then proves generation. No representation-theoretic irreducibility
or invariant-theory assertion is assumed.
-/

@[expose] public section

namespace GaussianTesting

open MvPolynomial

noncomputable section

def copyExponentDegree {m : ℕ} (a : Fin 2) (d : (Fin 2 × Fin m) →₀ ℕ) : ℕ :=
  ∑ i, d (a, i)

def copyExponentFactorial {m : ℕ} (d : (Fin 2 × Fin m) →₀ ℕ) : ℕ :=
  ∏ ai, (d ai).factorial

def copyExponentSwap {m : ℕ} (d : (Fin 2 × Fin m) →₀ ℕ) : (Fin 2 × Fin m) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun ai => d (ai.1.rev, ai.2))

@[simp] theorem copyExponentSwap_apply {m : ℕ}
    (d : (Fin 2 × Fin m) →₀ ℕ) (a : Fin 2) (i : Fin m) :
    copyExponentSwap d (a, i) = d (a.rev, i) := by simp [copyExponentSwap]

@[simp] theorem copyExponentSwap_swap {m : ℕ} (d : (Fin 2 × Fin m) →₀ ℕ) :
    copyExponentSwap (copyExponentSwap d) = d := by
  ext ai
  simp [copyExponentSwap, Fin.rev_rev]

theorem copyExponentDegree_swap {m : ℕ} (a : Fin 2) (d : (Fin 2 × Fin m) →₀ ℕ) :
    copyExponentDegree a (copyExponentSwap d) = copyExponentDegree a.rev d := by
  simp only [copyExponentDegree, copyExponentSwap_apply]

theorem copyExponentFactorial_pos {m : ℕ} (d : (Fin 2 × Fin m) →₀ ℕ) :
    0 < copyExponentFactorial d :=
  Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

theorem copyExponentFactorial_swap {m : ℕ} (d : (Fin 2 × Fin m) →₀ ℕ) :
    copyExponentFactorial (copyExponentSwap d) = copyExponentFactorial d := by
  simp [copyExponentFactorial, Fintype.prod_prod_type, Fin.prod_univ_two, mul_comm]

theorem copyExponentDegree_add_single {m : ℕ} (a b : Fin 2) (i : Fin m)
    (d : (Fin 2 × Fin m) →₀ ℕ) :
    copyExponentDegree b (d + Finsupp.single (a, i) 1) =
      copyExponentDegree b d + if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [copyExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib,
      Finsupp.single_apply, Prod.mk.injEq]
  · simp [copyExponentDegree, Finsupp.add_apply, Prod.mk.injEq, h]

theorem copyExponentFactorial_add_single {m : ℕ} (a : Fin 2) (i : Fin m)
    (d : (Fin 2 × Fin m) →₀ ℕ) :
    copyExponentFactorial (d + Finsupp.single (a, i) 1) =
      (d (a, i) + 1) * copyExponentFactorial d := by
  classical
  have h (bi : Fin 2 × Fin m) : ((d + Finsupp.single (a, i) 1 : (Fin 2 × Fin m) →₀ ℕ) bi).factorial =
      (if bi = (a, i) then d (a, i) + 1 else 1) * (d bi).factorial := by
    by_cases hbi : bi = (a, i)
    · subst bi
      simp [Nat.factorial_succ]
    · simp [hbi]
  simp only [copyExponentFactorial, h, Finset.prod_mul_distrib]
  simp

theorem copyModeSwap_monomial {m : ℕ} (d : (Fin 2 × Fin m) →₀ ℕ) (c : ℂ) :
    copyModeSwap m (monomial d c) = monomial (copyExponentSwap d) c := by
  rw [copyModeSwap, rename_monomial]
  apply congrArg (fun e : (Fin 2 × Fin m) →₀ ℕ => monomial e c)
  ext ⟨a, i⟩
  have hinj : Function.Injective (fun ai : Fin 2 × Fin m => (ai.1.rev, ai.2)) := by
    intro x y h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (Fin.rev_injective h₁) h₂
  have h := Finsupp.mapDomain_apply_of_injective hinj d (a.rev, i)
  simpa only [Fin.rev_rev, copyExponentSwap_apply] using h

theorem coeff_copyModeSwap {m : ℕ} (p : MvPolynomial (Fin 2 × Fin m) ℂ)
    (d : (Fin 2 × Fin m) →₀ ℕ) :
    (copyModeSwap m p).coeff d = p.coeff (copyExponentSwap d) := by
  induction p using MvPolynomial.induction_on' with
  | monomial q c =>
    rw [copyModeSwap_monomial]
    have h : copyExponentSwap q = d ↔ q = copyExponentSwap d := by
      constructor <;> intro h <;> simpa using congrArg copyExponentSwap h
    simp [coeff_monomial, h]
  | add p q hp hq => simp [map_add, hp, hq]

theorem copyModeEuler_monomial {m : ℕ} (a : Fin 2)
    (d : (Fin 2 × Fin m) →₀ ℕ) (c : ℂ) :
    copyModeEuler m a (monomial d c) = (copyExponentDegree a d : ℂ) • monomial d c := by
  simp only [copyModeEuler, X_mul_pderiv_monomial, ← Finset.sum_smul]
  rw [Nat.cast_smul_eq_nsmul]
  rfl

theorem coeff_copyModeEuler {m : ℕ} (a : Fin 2)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) (d : (Fin 2 × Fin m) →₀ ℕ) :
    (copyModeEuler m a p).coeff d = (copyExponentDegree a d : ℂ) * p.coeff d := by
  induction p using MvPolynomial.induction_on' with
  | monomial q c =>
    rw [copyModeEuler_monomial, coeff_smul]
    by_cases h : q = d
    · subst q
      simp
    · simp [coeff_monomial, h]
  | add p q hp hq =>
    have hadd : copyModeEuler m a (p + q) = copyModeEuler m a p + copyModeEuler m a q := by
      simp [copyModeEuler, map_add, mul_add, Finset.sum_add_distrib]
    simp [hadd, hp, hq, mul_add]

theorem finite_balanced_exponents (m k : ℕ) :
    {d : (Fin 2 × Fin m) →₀ ℕ | copyExponentDegree 0 d = k ∧
      copyExponentDegree 1 d = k}.Finite := by
  apply (Finsupp.finite_of_degree_eq (σ := Fin 2 × Fin m) (2 * k)).subset
  rintro d ⟨h₀, h₁⟩
  change d.degree = 2 * k
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Fin.sum_univ_two]
  change copyExponentDegree 0 d + copyExponentDegree 1 d = 2 * k
  omega

/-- The degree-`(k,k)` Fischer polynomial representing a linear functional.
The factorials are the coefficient weights adjoint to multiplication by a
variable and ordinary partial differentiation. -/
def balancedDualPolynomial (m k : ℕ)
    (L : MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] ℂ) :
    MvPolynomial (Fin 2 × Fin m) ℂ := by
  classical
  exact .ofCoeff (Finsupp.onFinset (finite_balanced_exponents m k).toFinset
    (fun d => if copyExponentDegree 0 d = k ∧ copyExponentDegree 1 d = k
      then L (monomial d 1) / (copyExponentFactorial d : ℂ) else 0)
    (fun d hd => by
      apply (finite_balanced_exponents m k).mem_toFinset.mpr
      by_contra h
      change ¬(copyExponentDegree 0 d = k ∧ copyExponentDegree 1 d = k) at h
      exact hd (by simp only [h, ite_false])))

theorem balancedDualPolynomial_coeff (m k : ℕ)
    (L : MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] ℂ) (d : (Fin 2 × Fin m) →₀ ℕ) :
    (balancedDualPolynomial m k L).coeff d =
      if copyExponentDegree 0 d = k ∧ copyExponentDegree 1 d = k
      then L (monomial d 1) / (copyExponentFactorial d : ℂ) else 0 := by
  classical
  rfl

theorem balancedDualPolynomial_euler (m k : ℕ)
    (L : MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] ℂ) (a : Fin 2) :
    copyModeEuler m a (balancedDualPolynomial m k L) = (k : ℂ) • balancedDualPolynomial m k L := by
  ext d
  rw [coeff_copyModeEuler, coeff_smul, balancedDualPolynomial_coeff]
  split_ifs with hd
  · fin_cases a <;> simp [hd.1, hd.2]
  · simp

theorem balancedDualPolynomial_swap (m k : ℕ)
    (L : MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] ℂ)
    (hL : ∀ p, L (copyModeSwap m p) = L p) :
    copyModeSwap m (balancedDualPolynomial m k L) = balancedDualPolynomial m k L := by
  ext d
  rw [coeff_copyModeSwap, balancedDualPolynomial_coeff, balancedDualPolynomial_coeff]
  simp only [copyExponentDegree_swap, copyExponentFactorial_swap,
    show (0 : Fin 2).rev = 1 from rfl, show (1 : Fin 2).rev = 0 from rfl, and_comm]
  rw [← copyModeSwap_monomial, hL]

theorem symmetricMixedPolynomial_swap (m : ℕ) (i j : Fin m) :
    copyModeSwap m (symmetricMixedPolynomial m i j) = symmetricMixedPolynomial m i j := by
  simp [symmetricMixedPolynomial, copyModeSwap_X, mul_comm, add_comm]

theorem copyModeSwap_eq_self_of_mem_symmetricMixedAlgebra {m : ℕ}
    {p : MvPolynomial (Fin 2 × Fin m) ℂ} (hp : p ∈ symmetricMixedAlgebra m) :
    copyModeSwap m p = p := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨⟨i,j⟩,rfl⟩ := hx; exact symmetricMixedPolynomial_swap m i j
  | algebraMap r => simp
  | add x y hx hy ix iy => simp [map_add, ix, iy]
  | mul x y hx hy ix iy => simp [map_mul, ix, iy]

theorem symmetricMixedPolynomial_mem (m : ℕ) (i j : Fin m) :
    symmetricMixedPolynomial m i j ∈ symmetricMixedAlgebra m :=
  Algebra.subset_adjoin ⟨(i,j),rfl⟩

/-- The Fischer coefficient identity: symmetric quadratic lowering is dual
to multiplication by the corresponding symmetric mixed quadratic. -/
theorem symmetricMixedLowering_balancedDualPolynomial_coeff (m k : ℕ)
    (L : MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] ℂ) (i j : Fin m)
    (d : (Fin 2 × Fin m) →₀ ℕ) :
    (symmetricMixedLowering m i j (balancedDualPolynomial m k L)).coeff d =
      if copyExponentDegree 0 d + 1 = k ∧ copyExponentDegree 1 d + 1 = k
      then L (symmetricMixedPolynomial m i j * monomial d 1) /
        (copyExponentFactorial d : ℂ) else 0 := by
  classical
  have hmon (a b : Fin m) :
      X (0, a) * X (1, b) * monomial d (1 : ℂ) =
        monomial (d + Finsupp.single (0, a) 1 + Finsupp.single (1, b) 1) 1 := by
    simp [X, monomial_mul_monomial, add_comm, add_assoc]
  have hi : (d (0, i) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d (0, i))
  have hj : (d (1, j) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d (1, j))
  have hi' : (d (1, i) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d (1, i))
  have hj' : (d (0, j) : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d (0, j))
  have hf : (copyExponentFactorial d : ℂ) ≠ 0 := by
    exact_mod_cast (copyExponentFactorial_pos d).ne'
  simp only [symmetricMixedLowering, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_pderiv,
    balancedDualPolynomial_coeff, copyExponentDegree_add_single,
    copyExponentFactorial_add_single]
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  norm_num
  split_ifs with hd
  · simp only [symmetricMixedPolynomial, add_mul, hmon, map_add]
    field_simp
  · simp

/-- Every symmetric mixed quadratic is fixed by interchange of the copies,
so an invariant functional annihilates a quadratic times a monomial whenever
it annihilates that quadratic times the symmetrized monomial. -/
theorem functional_quadratic_monomial_eq_zero {m : ℕ}
    (L : MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] ℂ)
    (hL : ∀ p, L (copyModeSwap m p) = L p) (i j : Fin m)
    (d : (Fin 2 × Fin m) →₀ ℕ)
    (hz : L (symmetricMixedPolynomial m i j *
      (monomial d 1 + monomial (copyExponentSwap d) 1)) = 0) :
    L (symmetricMixedPolynomial m i j * monomial d 1) = 0 := by
  have h := hL (symmetricMixedPolynomial m i j * monomial d 1)
  rw [map_mul, symmetricMixedPolynomial_swap, copyModeSwap_monomial] at h
  rw [mul_add, map_add, h] at hz
  linear_combination hz / 2

/-- Every symmetrized balanced monomial is a polynomial in the symmetric
mixed quadratics. This is the finite algebraic generation step. -/
theorem symmetric_balanced_monomial_mem (m k : ℕ)
    (d : (Fin 2 × Fin m) →₀ ℕ)
    (hd₀ : copyExponentDegree 0 d = k) (hd₁ : copyExponentDegree 1 d = k) :
    monomial d (1 : ℂ) + monomial (copyExponentSwap d) 1 ∈ symmetricMixedAlgebra m := by
  classical
  induction k using Nat.strong_induction_on generalizing d with
  | h k ih =>
    by_cases hk : k = 0
    · have hd : d = 0 := by
        ext ⟨a,i⟩
        have h₀ : ∀ i, d (0,i) = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp (hd₀.trans hk)
            i (Finset.mem_univ i)
        have h₁ : ∀ i, d (1,i) = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp (hd₁.trans hk)
            i (Finset.mem_univ i)
        fin_cases a <;> simp [h₀, h₁]
      subst d
      have hz : copyExponentSwap (0 : (Fin 2 × Fin m) →₀ ℕ) = 0 := by
        ext ai
        simp [copyExponentSwap]
      simpa only [hz, monomial_zero', map_one] using
        (symmetricMixedAlgebra m).add_mem (symmetricMixedAlgebra m).one_mem
          (symmetricMixedAlgebra m).one_mem
    · by_contra hnot
      obtain ⟨ell, hell, hA⟩ :=
        (symmetricMixedAlgebra m).toSubmodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
      let L : MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] ℂ :=
        ell + ell.comp (copyModeSwap m).toLinearMap
      have hL (p) : L (copyModeSwap m p) = L p := by
        simp [L, copyModeSwap_involutive, add_comm]
      have hellzero (p : MvPolynomial (Fin 2 × Fin m) ℂ)
          (hp : p ∈ symmetricMixedAlgebra m) : ell p = 0 := by
        have hh : ell p ∈ (symmetricMixedAlgebra m).toSubmodule.map ell :=
          ⟨p,hp,rfl⟩
        rw [hA] at hh
        exact hh
      have hLzero (p : MvPolynomial (Fin 2 × Fin m) ℂ)
          (hp : p ∈ symmetricMixedAlgebra m) : L p = 0 := by
        simp [L, copyModeSwap_eq_self_of_mem_symmetricMixedAlgebra hp, hellzero p hp]
      have hlow (i j : Fin m) :
          symmetricMixedLowering m i j (balancedDualPolynomial m k L) = 0 := by
        ext r
        rw [symmetricMixedLowering_balancedDualPolynomial_coeff]
        split_ifs with hr
        · have hr₀ : copyExponentDegree 0 r = k - 1 := by omega
          have hr₁ : copyExponentDegree 1 r = k - 1 := by omega
          have hm := ih (k - 1) (by omega) r hr₀ hr₁
          have hz := hLzero _ ((symmetricMixedAlgebra m).mul_mem
            (symmetricMixedPolynomial_mem m i j) hm)
          rw [functional_quadratic_monomial_eq_zero L hL i j r hz]
          simp
        · simp
      have hzero := symmetricMixedLowering_jointKernel_eq_zero (balancedDualPolynomial m k L)
        k (Nat.pos_of_ne_zero hk) (balancedDualPolynomial_euler m k L 0)
        (balancedDualPolynomial_euler m k L 1) (balancedDualPolynomial_swap m k L hL) hlow
      have hc := congrArg (fun p : MvPolynomial (Fin 2 × Fin m) ℂ => p.coeff d) hzero
      simp only [balancedDualPolynomial_coeff, hd₀, hd₁, and_self, ite_true] at hc
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
      have hf : (copyExponentFactorial d : ℂ) ≠ 0 := by
        exact_mod_cast (copyExponentFactorial_pos d).ne'
      have hLm : L (monomial d 1) = 0 := (div_eq_zero_iff.mp hc).resolve_right hf
      apply hell
      simpa [L, copyModeSwap_monomial, map_add] using hLm

/-- A polynomial invariant under the copy-rotation Euler generator and copy
interchange is generated by the symmetric mixed quadratic invariants. -/
theorem mem_symmetricMixedAlgebra_of_balanced_swap {m : ℕ}
    (p : MvPolynomial (Fin 2 × Fin m) ℂ)
    (hbal : copyModeEuler m 0 p = copyModeEuler m 1 p)
    (hswap : copyModeSwap m p = p) : p ∈ symmetricMixedAlgebra m := by
  classical
  have hd (d : (Fin 2 × Fin m) →₀ ℕ) (hd : d ∈ p.support) :
      copyExponentDegree 0 d = copyExponentDegree 1 d := by
    have hc := congrArg (fun q : MvPolynomial (Fin 2 × Fin m) ℂ => q.coeff d) hbal
    rw [coeff_copyModeEuler, coeff_copyModeEuler] at hc
    have hc' := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hd) hc
    exact_mod_cast hc'
  have hsum : p + copyModeSwap m p = ∑ d ∈ p.support,
      p.coeff d • (monomial d 1 + monomial (copyExponentSwap d) 1) := by
    have h₁ := p.as_sum
    have h₂ := congrArg (copyModeSwap m) p.as_sum
    simp only [map_sum, copyModeSwap_monomial] at h₂
    calc
      p + copyModeSwap m p =
          (∑ d ∈ p.support, monomial d (p.coeff d)) +
          (∑ d ∈ p.support, monomial (copyExponentSwap d) (p.coeff d)) :=
        congrArg₂ (· + ·) h₁ h₂
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _
        simp [smul_add, smul_monomial]
  have hmem : p + copyModeSwap m p ∈ symmetricMixedAlgebra m := by
    rw [hsum]
    apply (symmetricMixedAlgebra m).toSubmodule.sum_mem
    intro d hd'
    exact (symmetricMixedAlgebra m).toSubmodule.smul_mem _
      (symmetric_balanced_monomial_mem m (copyExponentDegree 0 d) d rfl (hd d hd').symm)
  have hhalf : (1 / 2 : ℂ) • (p + copyModeSwap m p) = p := by
    rw [hswap]
    module
  rw [← hhalf]
  exact (symmetricMixedAlgebra m).toSubmodule.smul_mem _ hmem

end

end GaussianTesting
