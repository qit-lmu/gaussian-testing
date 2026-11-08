module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.Lambda

@[expose] public section

/-!
# Creation, annihilation and number operators in occupation coordinates

These are the Jordan--Wigner formulas used in the Section 5 proof. The
creation and annihilation operators reconstruct the prescribed Majoranas,
and their product is the occupation number observable.
-/

namespace GaussianTesting

open Finset
open scoped InnerProductSpace

noncomputable section

variable {m : ℕ}

/-- The annihilation operator `(c_X + i c_Y)/2`. -/
def fermionAnnihilation (k : Fin m) : HF m →ₗ[ℂ] HF m :=
  (1 / 2 : ℂ) • (maj (k, false) + Complex.I • maj (k, true))

/-- The creation operator `(c_X - i c_Y)/2`. -/
def fermionCreation (k : Fin m) : HF m →ₗ[ℂ] HF m :=
  (1 / 2 : ℂ) • (maj (k, false) - Complex.I • maj (k, true))

theorem fermionAnnihilation_apply (k : Fin m) (f : HF m) (x : Qm m) :
    fermionAnnihilation k f x =
      if x k then 0 else jwSign x k * f (flipBit k x) := by
  cases hx : x k <;>
    simp [fermionAnnihilation, maj_apply, majFactor, hx] <;> ring_nf
  all_goals simp
  all_goals ring

theorem fermionCreation_apply (k : Fin m) (f : HF m) (x : Qm m) :
    fermionCreation k f x =
      if x k then jwSign x k * f (flipBit k x) else 0 := by
  cases hx : x k <;>
    simp [fermionCreation, maj_apply, majFactor, hx] <;> ring_nf
  all_goals simp
  all_goals ring

private theorem jwSign_flip_self (k : Fin m) (x : Qm m) :
    jwSign (flipBit k x) k = jwSign x k := by
  unfold jwSign
  apply Finset.prod_congr rfl
  intro l hl
  have hne : l ≠ k := ne_of_lt (Finset.mem_filter.mp hl).2
  simp [flipBit, Function.update_of_ne hne]

private theorem jwSign_sq (k : Fin m) (x : Qm m) : jwSign x k * jwSign x k = 1 := by
  unfold jwSign
  rw [← Finset.prod_mul_distrib]
  have h (l : Fin m) :
      (if x l then (-1 : ℂ) else 1) * (if x l then (-1 : ℂ) else 1) = 1 := by
    cases x l <;> norm_num
  simp only [h, Finset.prod_const_one]

/-- The occupation number operator `N_k = a_k† a_k`. -/
def fermionNumber (k : Fin m) : HF m →ₗ[ℂ] HF m :=
  fermionCreation k ∘ₗ fermionAnnihilation k

@[simp] theorem fermionNumber_apply (k : Fin m) (f : HF m) (x : Qm m) :
    fermionNumber k f x = if x k then f x else 0 := by
  simp only [fermionNumber, LinearMap.comp_apply, fermionCreation_apply,
    fermionAnnihilation_apply]
  have hxflip : flipBit k x k = !x k := by simp [flipBit]
  rw [hxflip, jwSign_flip_self, flipBit_flipBit]
  cases x k <;> simp [← mul_assoc, jwSign_sq]

/-- The occupation basis diagonalizes every number operator. -/
theorem fermionNumber_single (k : Fin m) (x : Qm m) :
    fermionNumber k (EuclideanSpace.single x (1 : ℂ)) =
      (if x k then (1 : ℂ) else 0) • EuclideanSpace.single x 1 := by
  ext y
  by_cases h : y = x
  · subst y; cases hx : x k <;> simp [hx]
  · cases x k <;> simp [EuclideanSpace.single, h]

/-- The first Majorana is the sum of creation and annihilation. -/
theorem fermionCreation_add_annihilation (k : Fin m) :
    fermionCreation k + fermionAnnihilation k = maj (k, false) := by
  ext f x
  simp only [LinearMap.add_apply, PiLp.add_apply, fermionCreation_apply,
    fermionAnnihilation_apply, maj_apply, majFactor]
  cases x k <;> simp

/-- The second Majorana is `i(a_k† - a_k)`. -/
theorem imaginary_fermionCreation_sub_annihilation (k : Fin m) :
    Complex.I • (fermionCreation k - fermionAnnihilation k) = maj (k, true) := by
  ext f x
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul, fermionCreation_apply,
    fermionAnnihilation_apply, maj_apply, majFactor]
  cases x k <;> simp <;> ring

/-- The signed occupation observable in the manuscript: `i c_X c_Y = 2N_k-I`. -/
theorem majorana_pair_eq_two_fermionNumber_sub_id (k : Fin m) :
    Complex.I • (maj (k, false) ∘ₗ maj (k, true)) =
      (2 : ℂ) • fermionNumber k - LinearMap.id := by
  ext f x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
    fermionNumber_apply, maj_apply, majFactor]
  rw [jwSign_flip_self, flipBit_flipBit]
  have hxflip : flipBit k x k = !x k := by simp [flipBit]
  rw [hxflip]
  cases hx : x k <;> simp <;> ring_nf <;> simp
  all_goals linear_combination (f x) * jwSign_sq k x

/-- The creation and annihilation formulas are adjoint to each other. -/
theorem fermionCreation_adjoint (k : Fin m) (f g : HF m) :
    inner ℂ (fermionCreation k f) g = inner ℂ f (fermionAnnihilation k g) := by
  simp only [fermionCreation, fermionAnnihilation, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, inner_smul_left, inner_sub_left,
    inner_add_right, inner_smul_right,
    map_div₀, map_one, map_ofNat, Complex.conj_I]
  rw [maj_isSymmetric (k, false), maj_isSymmetric (k, true)]
  ring

/-- One mode's contribution to the Gaussianity test in creation and
annihilation notation. -/
theorem majorana_tensor_pair_eq_ladder (k : Fin m) :
    opL (maj (k, false)) ∘ₗ opR (maj (k, false)) +
      opL (maj (k, true)) ∘ₗ opR (maj (k, true)) =
    (2 : ℂ) • (opL (fermionCreation k) ∘ₗ opR (fermionAnnihilation k) +
      opL (fermionAnnihilation k) ∘ₗ opR (fermionCreation k)) := by
  ext f ⟨x, y⟩
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  change
    maj (k, false) (WithLp.toLp 2 fun u =>
      maj (k, false) (WithLp.toLp 2 fun v => f (u, v)) y) x +
    maj (k, true) (WithLp.toLp 2 fun u =>
      maj (k, true) (WithLp.toLp 2 fun v => f (u, v)) y) x = _
  simp only [opL, opR, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    fermionCreation_apply, fermionAnnihilation_apply, maj_apply, majFactor]
  cases x k <;> cases y k <;> simp <;>
    ring_nf <;> simp <;> ring

/-- The manuscript's creation/annihilation expression for `Λ`. -/
theorem lambdaF_eq_ladder (m : ℕ) :
    lambdaF m = (2 : ℂ) • ∑ k : Fin m,
      (opL (fermionCreation k) ∘ₗ opR (fermionAnnihilation k) +
       opL (fermionAnnihilation k) ∘ₗ opR (fermionCreation k)) := by
  simp only [lambdaF, Fintype.sum_prod_type, Fintype.sum_bool, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [add_comm]
  exact majorana_tensor_pair_eq_ladder k


end
end GaussianTesting
