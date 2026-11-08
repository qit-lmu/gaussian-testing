module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerCore
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
# Creation polynomials and the finite number-vector core

The canonical commutation relations on polynomial Gaussian wavefunctions
show that creation words span every polynomial. Commutation of the creation
operators relates these words to the ordered powers defining the manuscript's
number vectors.
-/

namespace GaussianTesting

open MvPolynomial

noncomputable section

variable {σ : Type*}

private theorem inv_sqrt_two_square :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2 = 1 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  field_simp
  exact hs.symm

/-- The creation operators commute on the finite polynomial Gaussian domain. -/
theorem polynomialCreation_commute (j k : σ) :
    Function.Commute (polynomialCreation j) (polynomialCreation k) := by
  classical
  intro p
  by_cases h : j = k
  · subst k; rfl
  simp only [polynomialCreation_apply, map_smul, map_sub, pderiv_mul,
    pderiv_X_of_ne h, pderiv_X_of_ne (Ne.symm h), zero_mul, zero_add,
    pderiv_comm j k]
  simp only [Algebra.smul_def]
  ring

/-- The canonical commutation relation on polynomial factors. -/
theorem polynomialAnnihilation_creation [DecidableEq σ] (j k : σ) (p : MvPolynomial σ ℂ) :
    polynomialAnnihilation j (polynomialCreation k p) =
      polynomialCreation k (polynomialAnnihilation j p) + if j = k then p else 0 := by
  by_cases h : j = k
  · subst k
    simp only [polynomialAnnihilation_apply, polynomialCreation_apply,
      map_smul, map_sub, pderiv_mul, pderiv_X_self, one_mul]
    have hs := inv_sqrt_two_square
    calc
      _ = ((Real.sqrt 2 : ℂ)⁻¹) •
          ((2 : ℂ) • (X j * (((Real.sqrt 2 : ℂ)⁻¹) • pderiv j p)) -
            ((Real.sqrt 2 : ℂ)⁻¹) • pderiv j (pderiv j p)) +
          (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2) • p := by
            simp only [Algebra.smul_def, map_mul, map_ofNat]; ring
      _ = _ := by rw [hs, one_smul]; simp [Algebra.smul_def]; ring
  · simp only [polynomialAnnihilation_apply, polynomialCreation_apply,
      map_smul, map_sub, pderiv_mul, pderiv_X_of_ne (Ne.symm h), zero_mul, zero_add,
      pderiv_comm j k, ite_eq_right h, add_zero]
    simp only [Algebra.smul_def]
    ring

/-- An arbitrary finite creation word applied to the vacuum polynomial. -/
def creationWord (l : List σ) : MvPolynomial σ ℂ :=
  l.foldr (fun j p => polynomialCreation j p) 1

@[simp] theorem creationWord_nil : creationWord ([] : List σ) = 1 := rfl

@[simp] theorem creationWord_cons (j : σ) (l : List σ) :
    creationWord (j :: l) = polynomialCreation j (creationWord l) := rfl

private def creationWordSpan : Submodule ℂ (MvPolynomial σ ℂ) :=
  Submodule.span ℂ (Set.range (creationWord (σ := σ)))

private theorem creationWord_mem (l : List σ) : creationWord l ∈ creationWordSpan :=
  Submodule.subset_span ⟨l, rfl⟩

private theorem creationWordSpan_creation (j : σ) {p : MvPolynomial σ ℂ}
    (hp : p ∈ creationWordSpan) : polynomialCreation j p ∈ creationWordSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨l,rfl⟩ := hp
    exact creationWord_mem (j::l)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using creationWordSpan.add_mem hp hq
  | smul a p _ hp => simpa only [map_smul] using creationWordSpan.smul_mem a hp

private theorem creationWord_annihilation (j : σ) (l : List σ) :
    polynomialAnnihilation j (creationWord l) ∈ creationWordSpan := by
  classical
  induction l with
  | nil => simp [polynomialAnnihilation_apply, creationWordSpan]
  | cons k l ih =>
    rw [creationWord_cons, polynomialAnnihilation_creation]
    apply creationWordSpan.add_mem (creationWordSpan_creation k ih)
    split_ifs
    · exact creationWord_mem l
    · exact creationWordSpan.zero_mem

private theorem creationWordSpan_annihilation (j : σ) {p : MvPolynomial σ ℂ}
    (hp : p ∈ creationWordSpan) : polynomialAnnihilation j p ∈ creationWordSpan := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨l,rfl⟩ := hp
    exact creationWord_annihilation j l
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using creationWordSpan.add_mem hp hq
  | smul a p _ hp => simpa only [map_smul] using creationWordSpan.smul_mem a hp

/-- Every polynomial is a finite linear combination of creation words. -/
theorem span_creationWord_eq_top :
    Submodule.span ℂ (Set.range (creationWord (σ := σ))) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  change p ∈ creationWordSpan
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [creationWord_nil, smul_eq_C_mul, mul_one] using
      creationWordSpan.smul_mem c (creationWord_mem ([] : List σ))
  | add p q hp hq => exact creationWordSpan.add_mem hp hq
  | mul_X p j hp =>
    have h := creationWordSpan.smul_mem ((Real.sqrt 2 : ℂ)⁻¹)
      (creationWordSpan.add_mem (creationWordSpan_creation j hp)
        (creationWordSpan_annihilation j hp))
    have he : ((Real.sqrt 2 : ℂ)⁻¹) •
        (polynomialCreation j p + polynomialAnnihilation j p) = p * X j := by
      simp only [polynomialCreation_apply, polynomialAnnihilation_apply]
      calc
        _ = (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * 2) •
          (X j * p) := by simp only [Algebra.smul_def, map_mul, map_ofNat]; ring
        _ = _ := by rw [inv_sqrt_two_square, one_smul, mul_comm]
    rwa [he] at h

private def orderedCreationWord [Fintype σ] (n : σ → ℕ) : List σ :=
  (List.finRange (Fintype.card σ)).flatMap fun i =>
    List.replicate (n ((Fintype.equivFin σ).symm i)) ((Fintype.equivFin σ).symm i)

private theorem count_orderedCreationWord [Fintype σ] [DecidableEq σ]
    (n : σ → ℕ) (j : σ) : (orderedCreationWord n).count j = n j := by
  rw [orderedCreationWord, List.count_flatMap,
    ← List.sum_toFinset _ (List.nodup_finRange _)]
  simp only [List.toFinset_finRange, Function.comp_apply, List.count_replicate, beq_iff_eq]
  rw [(Fintype.equivFin σ).symm.sum_comp (fun k => if k = j then n k else 0)]
  simp

private theorem foldr_replicate_creation (j : σ) (n : ℕ) (p : MvPolynomial σ ℂ) :
    (List.replicate n j).foldr (fun k q => polynomialCreation k q) p =
      (polynomialCreation j)^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.foldr_cons, ih,
      Function.iterate_succ_apply']

private theorem orderedCreationWord_eq_raw [Fintype σ] (n : σ → ℕ) :
    creationWord (orderedCreationWord n) = fockNumberPolynomialRaw n := by
  rw [creationWord, orderedCreationWord, List.foldr_flatMap]
  simp_rw [foldr_replicate_creation]
  rfl

/-- Every occupation vector has a creation word with exactly its prescribed
mode multiplicities. -/
theorem exists_creationWord_eq_raw [Fintype σ] [DecidableEq σ] (n : σ → ℕ) :
    ∃ l : List σ, (∀ j, l.count j = n j) ∧
      creationWord l = fockNumberPolynomialRaw n :=
  ⟨orderedCreationWord n, count_orderedCreationWord n, orderedCreationWord_eq_raw n⟩

/-- Commuting creation operators put any creation word into the manuscript's
ordered powers, with exponents counting occurrences of each mode. -/
theorem creationWord_eq_fockNumberPolynomialRaw [Fintype σ] [DecidableEq σ]
    (l : List σ) : creationWord l = fockNumberPolynomialRaw (fun j => l.count j) := by
  have hp : l.Perm (orderedCreationWord (fun j => l.count j)) :=
    List.perm_iff_count.mpr fun j => (count_orderedCreationWord (fun k => l.count k) j).symm
  rw [← orderedCreationWord_eq_raw]
  exact hp.foldr_eq' (fun j _ k _ p => polynomialCreation_commute k j p) 1

/-- Ordered creation powers span the complete polynomial algebra. -/
theorem span_fockNumberPolynomialRaw_eq_top [Fintype σ] :
    Submodule.span ℂ (Set.range (fockNumberPolynomialRaw (σ := σ))) = ⊤ := by
  classical
  apply top_unique
  rw [← span_creationWord_eq_top]
  apply Submodule.span_le.mpr
  rintro p ⟨l,rfl⟩
  rw [creationWord_eq_fockNumberPolynomialRaw]
  exact Submodule.subset_span ⟨_,rfl⟩

/-- The specified finite number-vector core is exactly all polynomial
Gaussians; factorial normalization does not change its algebraic span. -/
theorem finiteFockPolynomialCore_eq_top (m : ℕ) : finiteFockPolynomialCore m = ⊤ := by
  apply top_unique
  rw [← span_fockNumberPolynomialRaw_eq_top]
  apply Submodule.span_le.mpr
  rintro p ⟨n,rfl⟩
  let c : ℂ := ((Real.pi ^ (-(2 * m : ℝ) / 4) /
    Real.sqrt (∏ i, (Nat.factorial (n i) : ℝ)) : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast ne_of_gt (div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.sqrt_pos.mpr (Finset.prod_pos fun i _ =>
        Nat.cast_pos.mpr (Nat.factorial_pos (n i)))))
  have h : fockNumberPolynomial m n ∈ finiteFockPolynomialCore m :=
    Submodule.subset_span ⟨n,rfl⟩
  have h' := (finiteFockPolynomialCore m).smul_mem c⁻¹ h
  change c⁻¹ • (c • fockNumberPolynomialRaw n) ∈ finiteFockPolynomialCore m at h'
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  exact h'

end
end GaussianTesting
