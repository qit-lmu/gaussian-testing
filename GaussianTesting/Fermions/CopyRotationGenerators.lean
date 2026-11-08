module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.SO3Bridge
public import GaussianTesting.Fermions.OccupationVacuum

@[expose] public section

/-!
# Infinitesimal copy rotations

The standard angle rotation from copy `r` towards copy `s` has skew-adjoint
generator `-1/2 ∑ c_(a,r)c_(a,s)`, equivalently `i L_rs/2`.
-/

namespace GaussianTesting

open Finset

noncomputable section

variable {m : ℕ}

/-- The vacuum on the three ordinary tensor factors. -/
def fermionTripleVacuum (m : ℕ) : H3 (Qm m) :=
  tp3 (fermionVacuum m) (fermionVacuum m) (fermionVacuum m)

theorem fermionTripleVacuum_ne_zero (m : ℕ) : fermionTripleVacuum m ≠ 0 := by
  intro h
  have hv := congrArg (fun f : H3 (Qm m) => f
    ((fun _ => false), (fun _ => false), (fun _ => false))) h
  simp [fermionTripleVacuum, tp3_apply, fermionVacuum, EuclideanSpace.single] at hv

/-- The infinitesimal copy rotation in the ordered coordinate plane `(r,s)`. -/
def fermionCopyGenerator (r s : Fin 3) : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) :=
  (-(2 : ℂ)⁻¹) • ∑ a : Fin m × Bool,
    fermionCubeMajorana r a * fermionCubeMajorana s a

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
theorem fermionCopyGenerator_comm (r s t : Fin 3) (hrs : r ≠ s) (b : Fin m × Bool) :
    fermionCopyGenerator r s * fermionCubeMajorana t b -
      fermionCubeMajorana t b * fermionCopyGenerator r s =
        if t = r then fermionCubeMajorana s b
        else if t = s then -fermionCubeMajorana r b else 0 := by
  classical
  have hterm (a : Fin m × Bool) :
      (fermionCubeMajorana r a * fermionCubeMajorana s a) * fermionCubeMajorana t b -
        fermionCubeMajorana t b * (fermionCubeMajorana r a * fermionCubeMajorana s a) =
      if a = b then
        if t = r then (-2 : ℂ) • fermionCubeMajorana s b
        else if t = s then (2 : ℂ) • fermionCubeMajorana r b else 0
      else 0 := by
    by_cases hab : a = b
    · subst a
      simp only [ite_true]
      by_cases htr : t = r
      · subst t
        simp only [ite_true]
        exact bivector_comm_left _ _ (fermionCubeMajorana_sq r b)
          (fermionCubeMajorana_anticomm r s b b (by simpa using hrs))
      · simp only [htr, ite_false]
        by_cases hts : t = s
        · subst t
          simp only [ite_true]
          exact bivector_comm_right _ _ (fermionCubeMajorana_sq s b)
            (fermionCubeMajorana_anticomm r s b b (by simpa using hrs))
        · simp only [hts, ite_false]
          exact bivector_comm_other _ _ _
            (fermionCubeMajorana_anticomm r t b b (by simpa using Ne.symm htr))
            (fermionCubeMajorana_anticomm s t b b (by simpa using Ne.symm hts))
    · simp only [hab, ite_false]
      exact bivector_comm_other _ _ _
        (fermionCubeMajorana_anticomm r t a b (by simp [hab]))
        (fermionCubeMajorana_anticomm s t a b (by simp [hab]))
  simp only [fermionCopyGenerator, smul_mul_assoc, mul_smul_comm,
    ← smul_sub, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp [smul_smul]

theorem fermionCopyGenerator12 :
    fermionCopyGenerator (m := m) 0 1 = (Complex.I / 2) • Lgen12 m := by
  simp only [fermionCopyGenerator, Lgen12, fermionCubeMajorana,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, Complex.I_mul_I]
  norm_num

theorem fermionCopyGenerator23 :
    fermionCopyGenerator (m := m) 1 2 = (Complex.I / 2) • Lgen23 m := by
  simp only [fermionCopyGenerator, Lgen23, fermionCubeMajorana,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, Complex.I_mul_I]
  norm_num

theorem fermionCopyGenerator13 :
    fermionCopyGenerator (m := m) 0 2 = (Complex.I / 2) • Lgen13 m := by
  simp only [fermionCopyGenerator, Lgen13, fermionCubeMajorana,
    Matrix.cons_val_zero, Matrix.cons_val_two, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, Complex.I_mul_I]
  norm_num

/-- Every pair generator kills the vacuum. -/
theorem fermionCopyGenerator_vacuum :
    fermionCopyGenerator (m := m) 0 1 (fermionTripleVacuum m) = 0 ∧
    fermionCopyGenerator (m := m) 1 2 (fermionTripleVacuum m) = 0 ∧
    fermionCopyGenerator (m := m) 0 2 (fermionTripleVacuum m) = 0 := by
  have h12 : p12 (lambdaF m) (fermionTripleVacuum m) = 0 := by
    ext x
    simp [fermionTripleVacuum, p12_tp3, fermionVacuum, lambdaF_tp2_basisState]
  have h23 : p23 (lambdaF m) (fermionTripleVacuum m) = 0 := by
    ext x
    simp [fermionTripleVacuum, p23_tp3, fermionVacuum, lambdaF_tp2_basisState]
  have h13 : p13 (lambdaF m) (fermionTripleVacuum m) = 0 := by
    ext x
    simp [fermionTripleVacuum, p13_tp3, fermionVacuum, lambdaF_tp2_basisState]
  simp [fermionCopyGenerator12, fermionCopyGenerator23, fermionCopyGenerator13,
    Lgen12_eq, Lgen23_eq, Lgen13_eq, LinearMap.comp_apply, h12, h23, h13]

end
end GaussianTesting
