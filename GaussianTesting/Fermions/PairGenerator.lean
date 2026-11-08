module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.PairCoordinates
public import GaussianTesting.Fermions.OccupationVacuum

@[expose] public section

/-!
# The two-copy fermionic rotation generator

The manuscript's `L = i ∑ c_(j,1)c_(j,2)` equals `-i (Π ⊗ I) Λ` and
has the same kernel as `Λ`. The standard-angle skew generator is `i L/2`.
-/

namespace GaussianTesting

open Finset

noncomputable section

variable {m : ℕ}

/-- The two-copy Hermitian generator `L` in Eq. (5.5). -/
def fermionPairL (m : ℕ) : Module.End ℂ (H2 (Qm m)) :=
  Complex.I • ∑ a : Fin m × Bool, maj2₁ a * maj2₂ a

private theorem opL_comp (A B : Module.End ℂ (HF m)) :
    opL A ∘ₗ opL B = opL (A ∘ₗ B) := by ext f x; rfl

private theorem opL_neg (A : Module.End ℂ (HF m)) : opL (-A) = -opL A := by ext f x; rfl

/-- The parity factor relating the two-copy generator and the test operator. -/
theorem fermionPairL_eq :
    fermionPairL m = (-Complex.I) • (opL (parityOp (m := m)) ∘ₗ lambdaF m) := by
  have ha (a : Fin m × Bool) : maj a ∘ₗ parityOp = -(parityOp ∘ₗ maj a) :=
    eq_neg_of_add_eq_zero_left (add_comm _ _ |>.trans (parityOp_anticomm_maj a))
  simp only [fermionPairL, maj2₁, maj2₂, Module.End.mul_eq_comp,
    ← LinearMap.comp_assoc, opL_comp, ha, opL_neg, LinearMap.neg_comp,
    Finset.sum_neg_distrib, smul_neg, neg_smul, lambdaF]
  simp only [← opL_comp, LinearMap.comp_assoc]
  congr 2
  ext f x
  simp [LinearMap.comp_apply, map_sum, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]

/-- Invertibility of parity gives exactly the same kernel as the test operator. -/
theorem ker_fermionPairL : LinearMap.ker (fermionPairL m) = LinearMap.ker (lambdaF m) := by
  rw [fermionPairL_eq, LinearMap.ker_smul _ _ (neg_ne_zero.mpr Complex.I_ne_zero)]
  have hp : opL (parityOp (m := m)) ∘ₗ opL parityOp = LinearMap.id := by
    rw [opL_comp, parityOp_sq]
    ext f x
    rfl
  ext f
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro h
    have hh := congrArg (opL parityOp) h
    change (opL parityOp ∘ₗ opL parityOp) (lambdaF m f) = opL parityOp 0 at hh
    simpa only [hp, LinearMap.id_apply, map_zero] using hh
  · intro h
    rw [h, map_zero]

/-- The standard-angle infinitesimal rotation from copy one towards copy two. -/
def fermionPairGenerator (m : ℕ) : Module.End ℂ (H2 (Qm m)) :=
  (Complex.I / 2) • fermionPairL m

/-- The nonzero scalar normalization does not change the fixed kernel. -/
theorem ker_fermionPairGenerator :
    LinearMap.ker (fermionPairGenerator m) = LinearMap.ker (lambdaF m) := by
  rw [fermionPairGenerator, LinearMap.ker_smul _ _
    (div_ne_zero Complex.I_ne_zero (by norm_num)), ker_fermionPairL]

/-- The vacuum on both ordinary tensor factors. -/
def fermionPairVacuum (m : ℕ) : H2 (Qm m) := tp2 (fermionVacuum m) (fermionVacuum m)

theorem fermionPairVacuum_ne_zero (m : ℕ) : fermionPairVacuum m ≠ 0 := by
  intro h
  have hv := congrArg (fun f : H2 (Qm m) => f ((fun _ => false), (fun _ => false))) h
  simp [fermionPairVacuum, tp2_apply, fermionVacuum, EuclideanSpace.single] at hv

/-- The pair generator kills the vacuum, fixing its scalar normalization. -/
theorem fermionPairGenerator_vacuum : fermionPairGenerator m (fermionPairVacuum m) = 0 := by
  have hv : lambdaF m (fermionPairVacuum m) = 0 := by
    simpa [fermionPairVacuum, fermionVacuum] using lambdaF_tp2_basisState (m := m)
  simp [fermionPairGenerator, fermionPairL_eq, LinearMap.comp_apply, hv]

private def pairInfinitesimal (r s : Fin 2) : Module.End ℂ (H2 (Qm m)) :=
  (-(2 : ℂ)⁻¹) • ∑ a : Fin m × Bool, fermionPairMajorana r a * fermionPairMajorana s a

private theorem pairMajorana_neg (r s : Fin 2) (a b : Fin m × Bool)
    (h : (r, a) ≠ (s, b)) :
    fermionPairMajorana r a * fermionPairMajorana s b =
      -(fermionPairMajorana s b * fermionPairMajorana r a) :=
  eq_neg_of_add_eq_zero_left (fermionPairMajorana_anticomm r s a b h)

private theorem bivector_comm_left {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A B : Module.End ℂ E) (hA : A * A = 1) (hAB : A * B = -(B * A)) :
    (A * B) * A - A * (A * B) = (-2 : ℂ) • B := by
  have hBA : B * A = -(A * B) := by simpa using (congrArg Neg.neg hAB).symm
  rw [mul_assoc, hBA, mul_neg, ← mul_assoc, hA, one_mul]
  simp only [neg_smul, two_smul]
  abel

private theorem bivector_comm_right {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A B : Module.End ℂ E) (hB : B * B = 1) (hAB : A * B = -(B * A)) :
    (A * B) * B - B * (A * B) = (2 : ℂ) • A := by
  have hBA : B * A = -(A * B) := by simpa using (congrArg Neg.neg hAB).symm
  rw [mul_assoc, hB, mul_one, ← mul_assoc, hBA, neg_mul, mul_assoc, hB, mul_one]
  simp [two_smul]

private theorem bivector_comm_other {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A B C : Module.End ℂ E)
    (hAC : A * C = -(C * A)) (hBC : B * C = -(C * B)) :
    (A * B) * C - C * (A * B) = 0 := by
  rw [mul_assoc, hBC, mul_neg, ← mul_assoc, hAC, neg_mul, neg_neg, mul_assoc, sub_self]

/-- Commuting the infinitesimal copy rotation with a Majorana gives the
ordinary one-particle infinitesimal rotation. -/
private theorem pairInfinitesimal_comm (r s t : Fin 2) (hrs : r ≠ s) (b : Fin m × Bool) :
    pairInfinitesimal r s * fermionPairMajorana t b -
      fermionPairMajorana t b * pairInfinitesimal r s =
        if t = r then fermionPairMajorana s b
        else if t = s then -fermionPairMajorana r b else 0 := by
  classical
  have hterm (a : Fin m × Bool) :
      (fermionPairMajorana r a * fermionPairMajorana s a) * fermionPairMajorana t b -
        fermionPairMajorana t b * (fermionPairMajorana r a * fermionPairMajorana s a) =
      if a = b then
        if t = r then (-2 : ℂ) • fermionPairMajorana s b
        else if t = s then (2 : ℂ) • fermionPairMajorana r b else 0
      else 0 := by
    by_cases hab : a = b
    · subst a
      simp only [ite_true]
      by_cases htr : t = r
      · subst t
        simp only [ite_true]
        exact bivector_comm_left _ _ (fermionPairMajorana_sq r b)
          (pairMajorana_neg r s b b (by simpa using hrs))
      · simp only [htr, ite_false]
        by_cases hts : t = s
        · subst t
          simp only [ite_true]
          exact bivector_comm_right _ _ (fermionPairMajorana_sq s b)
            (pairMajorana_neg r s b b (by simpa using hrs))
        · simp only [hts, ite_false]
          exact bivector_comm_other _ _ _
            (pairMajorana_neg r t b b (by simpa using Ne.symm htr))
            (pairMajorana_neg s t b b (by simpa using Ne.symm hts))
    · simp only [hab, ite_false]
      exact bivector_comm_other _ _ _
        (pairMajorana_neg r t a b (by simp [hab]))
        (pairMajorana_neg s t a b (by simp [hab]))
  simp only [pairInfinitesimal, smul_mul_assoc, mul_smul_comm,
    ← smul_sub, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp [smul_smul]

/-- The generator acts on the two Majorana families by the ordinary
infinitesimal rotation of their copy index. -/
theorem fermionPairGenerator_comm (r : Fin 2) (b : Fin m × Bool) :
    fermionPairGenerator m * fermionPairMajorana r b -
      fermionPairMajorana r b * fermionPairGenerator m =
        if r = 0 then fermionPairMajorana 1 b else -fermionPairMajorana 0 b := by
  have hg : fermionPairGenerator m = pairInfinitesimal 0 1 := by
    simp only [fermionPairGenerator, fermionPairL, pairInfinitesimal,
      fermionPairMajorana, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
    congr 1
    rw [div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  rw [hg]
  have h := pairInfinitesimal_comm 0 1 r (by decide) b
  fin_cases r <;> simpa using h

end
end GaussianTesting
