module

/-
The fermionic Fock space on m modes in its Jordan–Wigner representation, and the
Majorana operators (Section 5 of the paper).

We realize `H_m ≅ (ℂ²)^{⊗m}` concretely as `EuclideanSpace ℂ (Fin m → Bool)` (basis
states = occupation bitstrings). The 2m Majorana operators are indexed by
`Fin m × Bool`:

    c_{k,false} = Z₁ ⋯ Z_{k-1} X_k     ("c_{2k-1}")
    c_{k,true}  = Z₁ ⋯ Z_{k-1} Y_k     ("c_{2k}")

acting on coordinates by `(maj (k,b) f)(x) = jwSign x k · majFactor b (x k) · f(x ⊕ eₖ)`.
They are Hermitian unitaries satisfying the canonical anticommutation relations
`{c_a, c_b} = 2 δ_{ab}` (lemmas `maj_isSymmetric`, `maj_sq`, `maj_anticomm`).
The parity operator is `Π = (-1)^N`, diagonal with sign `(-1)^{|x|}`.
-/
public import GaussianTesting.GradientFlow.Defs

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {m : ℕ}

/-- Occupation bitstrings: the standard basis index of the m-mode Fock space. -/
abbrev Qm (m : ℕ) := Fin m → Bool

/-- The m-mode fermionic Fock space in Jordan–Wigner form. -/
abbrev HF (m : ℕ) := H (Qm m)

/-- The Jordan–Wigner string sign `(-1)^{#{l < k : x l}}`. -/
def jwSign (x : Qm m) (k : Fin m) : ℂ :=
  ∏ l ∈ univ.filter (fun l => l < k), (if x l then -1 else 1)

/-- The on-site factor: `1` for X-type Majoranas, `±i` for Y-type. -/
def majFactor (b : Bool) (bit : Bool) : ℂ :=
  if b then (if bit then Complex.I else -Complex.I) else 1

/-- Flip the k-th bit. -/
def flipBit (k : Fin m) (x : Qm m) : Qm m := Function.update x k (!x k)

@[simp] lemma flipBit_flipBit (k : Fin m) (x : Qm m) : flipBit k (flipBit k x) = x := by
  simp [flipBit, Function.update_idem]

/-- The Majorana operator `c_{k,b}` in Jordan–Wigner form. -/
def maj (a : Fin m × Bool) : HF m →ₗ[ℂ] HF m where
  toFun f := WithLp.toLp 2 fun x => jwSign x a.1 * majFactor a.2 (x a.1) * f (flipBit a.1 x)
  map_add' f g := by
    ext x
    simp only [PiLp.add_apply]
    ring
  map_smul' c f := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma maj_apply (a : Fin m × Bool) (f : HF m) (x : Qm m) :
    maj a f x = jwSign x a.1 * majFactor a.2 (x a.1) * f (flipBit a.1 x) := rfl

private lemma flipBit_apply_ne (k l : Fin m) (x : Qm m) (h : l ≠ k) :
    flipBit k x l = x l := by simp [flipBit, Function.update_of_ne h]

private lemma flipBit_apply_self (k : Fin m) (x : Qm m) :
    flipBit k x k = !x k := by simp [flipBit]

private lemma flipBit_comm (k l : Fin m) (x : Qm m) (h : k ≠ l) :
    flipBit k (flipBit l x) = flipBit l (flipBit k x) := by
  ext j
  by_cases hj : j = k
  · subst j; simp [flipBit, Function.update_of_ne h]
  · by_cases hj' : j = l
    · subst j; simp [flipBit, Function.update_of_ne h.symm]
    · simp [flipBit, Function.update_of_ne hj, Function.update_of_ne hj']

private lemma sign_sq (bit : Bool) :
    (if bit then (-1 : ℂ) else 1) * (if bit then (-1 : ℂ) else 1) = 1 := by
  cases bit <;> norm_num

private lemma sign_flip (bit : Bool) :
    (if !bit then (-1 : ℂ) else 1) = -(if bit then (-1 : ℂ) else 1) := by
  cases bit <;> norm_num

private lemma signProd_flip (s : Finset (Fin m)) (x : Qm m) (l : Fin m)
    (hl : l ∈ s) :
    (∏ j ∈ s, (if flipBit l x j then (-1 : ℂ) else 1)) =
      -(∏ j ∈ s, (if x j then (-1 : ℂ) else 1)) := by
  rw [← Finset.mul_prod_erase s _ hl, ← Finset.mul_prod_erase s _ hl]
  rw [flipBit_apply_self, sign_flip]
  have he : (∏ j ∈ s.erase l, (if flipBit l x j then (-1 : ℂ) else 1)) =
      ∏ j ∈ s.erase l, (if x j then (-1 : ℂ) else 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [flipBit_apply_ne l j x (Finset.mem_erase.mp hj).1]
  rw [he]; ring

private lemma jwSign_flipBit_of_le (x : Qm m) {k l : Fin m} (h : k ≤ l) :
    jwSign (flipBit l x) k = jwSign x k := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [flipBit_apply_ne l j x (ne_of_lt (lt_of_lt_of_le (Finset.mem_filter.mp hj).2 h))]

private lemma jwSign_flipBit_of_lt (x : Qm m) {k l : Fin m} (h : l < k) :
    jwSign (flipBit l x) k = -jwSign x k := by
  exact signProd_flip _ x l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

private lemma jwSign_mul_self (x : Qm m) (k : Fin m) :
    jwSign x k * jwSign x k = 1 := by
  rw [jwSign, ← Finset.prod_mul_distrib]
  simp only [sign_sq, Finset.prod_const_one]

private lemma jwSign_conj (x : Qm m) (k : Fin m) :
    starRingEnd ℂ (jwSign x k) = jwSign x k := by
  simp only [jwSign, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> simp

private lemma majFactor_mul (b bit : Bool) :
    majFactor b bit * majFactor b (!bit) = 1 := by
  cases b <;> cases bit <;> simp [majFactor, Complex.I_mul_I]

private lemma majFactor_conj (b bit : Bool) :
    starRingEnd ℂ (majFactor b bit) = majFactor b (!bit) := by
  cases b <;> cases bit <;> simp [majFactor]

/-- Majorana operators are Hermitian. -/
lemma maj_isSymmetric (a : Fin m × Bool) : (maj a).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, maj_apply, map_mul,
    jwSign_conj, majFactor_conj]
  rw [← Fintype.sum_bijective (flipBit a.1)
    (Function.Involutive.bijective (flipBit_flipBit a.1))]
  intro x
  simp only [flipBit_flipBit, jwSign_flipBit_of_le x (le_refl a.1),
    flipBit_apply_self, Bool.not_not]
  ring

/-- Majorana operators square to the identity: `c_a² = 1`. -/
lemma maj_sq (a : Fin m × Bool) : maj a ∘ₗ maj a = LinearMap.id := by
  ext f x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, maj_apply,
    jwSign_flipBit_of_le x (le_refl a.1), flipBit_apply_self, flipBit_flipBit]
  calc
    _ = (jwSign x a.1 * jwSign x a.1) *
      (majFactor a.2 (x a.1) * majFactor a.2 (!(x a.1))) * f x := by ring
    _ = f x := by rw [jwSign_mul_self, majFactor_mul]; ring

/-- Distinct Majorana operators anticommute: `{c_a, c_b} = 0` for `a ≠ b`. -/
lemma maj_anticomm {a b : Fin m × Bool} (hab : a ≠ b) :
    maj a ∘ₗ maj b + maj b ∘ₗ maj a = 0 := by
  rcases a with ⟨k, c⟩
  rcases b with ⟨l, d⟩
  ext f x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, PiLp.add_apply,
    LinearMap.zero_apply, PiLp.zero_apply, maj_apply]
  by_cases h : k = l
  · subst l
    have hcd : c ≠ d := by intro h; subst d; exact hab rfl
    simp only [jwSign_flipBit_of_le x (le_refl k), flipBit_apply_self, flipBit_flipBit]
    cases c <;> cases d <;> cases hx : x k <;>
      simp_all [majFactor] <;> ring
  · rw [flipBit_apply_ne l k x h, flipBit_apply_ne k l x (Ne.symm h),
      flipBit_comm k l x h]
    rcases lt_or_gt_of_ne h with hlt | hlt
    · rw [jwSign_flipBit_of_le x (le_of_lt hlt), jwSign_flipBit_of_lt x hlt]
      ring
    · rw [jwSign_flipBit_of_lt x hlt, jwSign_flipBit_of_le x (le_of_lt hlt)]
      ring

/-- The parity operator `Π = (-1)^N`, diagonal in the occupation basis. -/
def parityOp : HF m →ₗ[ℂ] HF m where
  toFun f := WithLp.toLp 2 fun x => (-1 : ℂ) ^ (univ.filter fun l => x l).card * f x
  map_add' f g := by
    ext x
    simp only [PiLp.add_apply]
    ring
  map_smul' c f := by
    ext x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma parityOp_apply (f : HF m) (x : Qm m) :
    parityOp f x = (-1 : ℂ) ^ (univ.filter fun l => x l).card * f x := rfl

private lemma parity_prod (x : Qm m) :
    (-1 : ℂ) ^ (univ.filter fun l => x l).card =
      ∏ l : Fin m, (if x l then (-1 : ℂ) else 1) := by
  rw [← Finset.prod_const]
  exact Finset.prod_filter _ _

private lemma parity_flip (x : Qm m) (k : Fin m) :
    (-1 : ℂ) ^ (univ.filter fun l => flipBit k x l).card =
      -(-1 : ℂ) ^ (univ.filter fun l => x l).card := by
  rw [parity_prod, parity_prod]
  exact signProd_flip univ x k (Finset.mem_univ _)

/-- The parity operator anticommutes with every Majorana operator. -/
lemma parityOp_anticomm_maj (a : Fin m × Bool) :
    parityOp ∘ₗ maj a + maj a ∘ₗ parityOp = 0 := by
  ext f x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, PiLp.add_apply,
    LinearMap.zero_apply, PiLp.zero_apply, parityOp_apply, maj_apply, parity_flip]
  ring

/-- The parity operator is an involution. -/
lemma parityOp_sq : (parityOp : HF m →ₗ[ℂ] HF m) ∘ₗ parityOp = LinearMap.id := by
  ext f x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, parityOp_apply]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

end

end GaussianTesting
