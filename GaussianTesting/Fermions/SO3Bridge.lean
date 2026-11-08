module

/-
The angular-momentum Lie-algebra structure on three copies of the fermionic Fock space (proof of
thm:main-fermions' spectral input, Section 5.2 of the paper).

Three-copy Majorana operators with Jordan–Wigner-style parity strings across copies:

    c_{a,1} = c_a ⊗ I ⊗ I,   c_{a,2} = Π ⊗ c_a ⊗ I,   c_{a,3} = Π ⊗ Π ⊗ c_a

satisfy the CAR; the rotation generators `L_ab = i Σ_a c_{a,A} c_{a,B}` halve to a
Hermitian angular-momentum triple (Jx, Jy, Jz) := (L₁₂, L₂₃, L₁₃)/2 with
`[Jx,Jy] = iJz` (cyclically), and `ker L_ab = ker Λ_ab` since `L_ab` equals `Λ_ab`
times an invertible (parity) factor. Finally `P_ab = p_ab(PF)` is the orthogonal
projection onto `ker Λ_ab`, so `Sop (PF) = kacT J` and `kacT_gap` yields
`SpectralGapHyp (PF m) (7/12)`.

Operator-slot algebra: `op1 A = A⊗I⊗I`, `op2 A = I⊗A⊗I`, `op3 A = I⊗I⊗A` are
multiplicative in each slot and commute across slots — all consequences of
`p12_comp`/`p23_comp`/`p13_comp` and `opL_opR_comm` (note `op2 A = p12 (opR A) =
p23 (opL A)` and `op1 A = p12 (opL A) = p13 (opL A)`, `op3 A = p23 (opR A) =
p13 (opR A)`, each provable by `ext`).
-/
public import GaussianTesting.Fermions.Lambda
public import GaussianTesting.GradientFlow.Moments
public import GaussianTesting.Kac.KacWalk

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {ι : Type*} [Fintype ι]

/-! ### Slot embeddings `End(H) → End(H^⊗3)` -/

/-- `A ⊗ I ⊗ I`. -/
def op1 (A : H ι →ₗ[ℂ] H ι) : H3 ι →ₗ[ℂ] H3 ι := p12 (opL A)

/-- `I ⊗ A ⊗ I`. -/
def op2 (A : H ι →ₗ[ℂ] H ι) : H3 ι →ₗ[ℂ] H3 ι := p12 (opR A)

/-- `I ⊗ I ⊗ A`. -/
def op3 (A : H ι →ₗ[ℂ] H ι) : H3 ι →ₗ[ℂ] H3 ι := p23 (opR A)

omit [Fintype ι] in
lemma op1_eq_p13 [Fintype ι] (A : H ι →ₗ[ℂ] H ι) : op1 A = p13 (opL A) := by
  rfl

omit [Fintype ι] in
lemma op2_eq_p23 [Fintype ι] (A : H ι →ₗ[ℂ] H ι) : op2 A = p23 (opL A) := by
  rfl

omit [Fintype ι] in
lemma op3_eq_p13 [Fintype ι] (A : H ι →ₗ[ℂ] H ι) : op3 A = p13 (opR A) := by
  rfl

omit [Fintype ι] in
lemma op1_comp [Fintype ι] (A B : H ι →ₗ[ℂ] H ι) : op1 A ∘ₗ op1 B = op1 (A ∘ₗ B) := by
  rfl

omit [Fintype ι] in
lemma op2_comp [Fintype ι] (A B : H ι →ₗ[ℂ] H ι) : op2 A ∘ₗ op2 B = op2 (A ∘ₗ B) := by
  rfl

omit [Fintype ι] in
lemma op3_comp [Fintype ι] (A B : H ι →ₗ[ℂ] H ι) : op3 A ∘ₗ op3 B = op3 (A ∘ₗ B) := by
  rfl

lemma op1_op2_comm (A B : H ι →ₗ[ℂ] H ι) : op1 A ∘ₗ op2 B = op2 B ∘ₗ op1 A := by
  simp only [op1, op2, p12_comp]
  rw [opL_opR_comm]

lemma op2_op3_comm (A B : H ι →ₗ[ℂ] H ι) : op2 A ∘ₗ op3 B = op3 B ∘ₗ op2 A := by
  rw [op2_eq_p23]
  simp only [op3, p23_comp]
  rw [opL_opR_comm]

lemma op1_op3_comm (A B : H ι →ₗ[ℂ] H ι) : op1 A ∘ₗ op3 B = op3 B ∘ₗ op1 A := by
  rw [op1_eq_p13, op3_eq_p13]
  simp only [p13_comp]
  rw [opL_opR_comm]

private lemma bridge_opL_isSymmetric {ι : Type*} [Fintype ι]
    {A : H ι →ₗ[ℂ] H ι} (hA : A.IsSymmetric) : (opL A).IsSymmetric := by
  intro f g
  have hi (u v : H2 ι) : inner ℂ u v =
      ∑ j, inner ℂ (WithLp.toLp 2 fun i => u (i, j))
        (WithLp.toLp 2 fun i => v (i, j)) := by
    simp only [PiLp.inner_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  rw [hi, hi]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [opL, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    WithLp.toLp_ofLp] using hA (WithLp.toLp 2 fun i => f (i, j))
      (WithLp.toLp 2 fun i => g (i, j))

private lemma bridge_opR_isSymmetric {ι : Type*} [Fintype ι]
    {A : H ι →ₗ[ℂ] H ι} (hA : A.IsSymmetric) : (opR A).IsSymmetric := by
  intro f g
  have hi (u v : H2 ι) : inner ℂ u v =
      ∑ i, inner ℂ (WithLp.toLp 2 fun j => u (i, j))
        (WithLp.toLp 2 fun j => v (i, j)) := by
    simp only [PiLp.inner_apply, Fintype.sum_prod_type]
  rw [hi, hi]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [opR, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    WithLp.toLp_ofLp] using hA (WithLp.toLp 2 fun j => f (i, j))
      (WithLp.toLp 2 fun j => g (i, j))

lemma op1_isSymmetric {A : H ι →ₗ[ℂ] H ι} (hA : A.IsSymmetric) :
    (op1 A).IsSymmetric := by
  exact p12_isSymmetric (bridge_opL_isSymmetric hA)

lemma op2_isSymmetric {A : H ι →ₗ[ℂ] H ι} (hA : A.IsSymmetric) :
    (op2 A).IsSymmetric := by
  exact p12_isSymmetric (bridge_opR_isSymmetric hA)

lemma op3_isSymmetric {A : H ι →ₗ[ℂ] H ι} (hA : A.IsSymmetric) :
    (op3 A).IsSymmetric := by
  exact p23_isSymmetric (bridge_opR_isSymmetric hA)

omit [Fintype ι] in
private lemma op1_neg [Fintype ι] (A : H ι →ₗ[ℂ] H ι) : op1 (-A : H ι →ₗ[ℂ] H ι) = -op1 A := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op1_id [Fintype ι]  : op1 (LinearMap.id : H ι →ₗ[ℂ] H ι) = LinearMap.id := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op1_zero [Fintype ι]  : op1 (0 : H ι →ₗ[ℂ] H ι) = 0 := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op2_neg [Fintype ι] (A : H ι →ₗ[ℂ] H ι) : op2 (-A : H ι →ₗ[ℂ] H ι) = -op2 A := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op2_id [Fintype ι]  : op2 (LinearMap.id : H ι →ₗ[ℂ] H ι) = LinearMap.id := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op2_zero [Fintype ι]  : op2 (0 : H ι →ₗ[ℂ] H ι) = 0 := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op3_neg [Fintype ι] (A : H ι →ₗ[ℂ] H ι) : op3 (-A : H ι →ₗ[ℂ] H ι) = -op3 A := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op3_id [Fintype ι]  : op3 (LinearMap.id : H ι →ₗ[ℂ] H ι) = LinearMap.id := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma op3_zero [Fintype ι]  : op3 (0 : H ι →ₗ[ℂ] H ι) = 0 := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p12_neg [Fintype ι] (A : H2 ι →ₗ[ℂ] H2 ι) : p12 (-A : H2 ι →ₗ[ℂ] H2 ι) = -p12 A := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p12_id [Fintype ι]  : p12 (LinearMap.id : H2 ι →ₗ[ℂ] H2 ι) = LinearMap.id := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p12_zero [Fintype ι]  : p12 (0 : H2 ι →ₗ[ℂ] H2 ι) = 0 := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p12_sum [Fintype ι] {κ : Type*} (t : Finset κ) (A : κ → H2 ι →ₗ[ℂ] H2 ι) :
    p12 (∑ a ∈ t, A a) = ∑ a ∈ t, p12 (A a) := by
  ext f x
  simp [p12, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [Fintype ι] in
private lemma p23_neg [Fintype ι] (A : H2 ι →ₗ[ℂ] H2 ι) : p23 (-A : H2 ι →ₗ[ℂ] H2 ι) = -p23 A := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p23_id [Fintype ι]  : p23 (LinearMap.id : H2 ι →ₗ[ℂ] H2 ι) = LinearMap.id := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p23_zero [Fintype ι]  : p23 (0 : H2 ι →ₗ[ℂ] H2 ι) = 0 := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p23_sum [Fintype ι] {κ : Type*} (t : Finset κ) (A : κ → H2 ι →ₗ[ℂ] H2 ι) :
    p23 (∑ a ∈ t, A a) = ∑ a ∈ t, p23 (A a) := by
  ext f x
  simp [p23, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]

omit [Fintype ι] in
private lemma p13_neg [Fintype ι] (A : H2 ι →ₗ[ℂ] H2 ι) : p13 (-A : H2 ι →ₗ[ℂ] H2 ι) = -p13 A := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p13_id [Fintype ι]  : p13 (LinearMap.id : H2 ι →ₗ[ℂ] H2 ι) = LinearMap.id := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p13_zero [Fintype ι]  : p13 (0 : H2 ι →ₗ[ℂ] H2 ι) = 0 := by
  ext f x
  rfl

omit [Fintype ι] in
private lemma p13_sum [Fintype ι] {κ : Type*} (t : Finset κ) (A : κ → H2 ι →ₗ[ℂ] H2 ι) :
    p13 (∑ a ∈ t, A a) = ∑ a ∈ t, p13 (A a) := by
  ext f x
  simp [p13, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]

/-! ### Three-copy Majorana operators (with parity strings) -/

variable {m : ℕ}

/-- `c_{a,1} = c_a ⊗ I ⊗ I`. -/
def maj3₁ (a : Fin m × Bool) : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) := op1 (maj a)

/-- `c_{a,2} = Π ⊗ c_a ⊗ I`. -/
def maj3₂ (a : Fin m × Bool) : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) :=
  op1 parityOp ∘ₗ op2 (maj a)

/-- `c_{a,3} = Π ⊗ Π ⊗ c_a`. -/
def maj3₃ (a : Fin m × Bool) : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) :=
  op1 parityOp ∘ₗ op2 parityOp ∘ₗ op3 (maj a)

/-- The parity-string Majorana in one of the three copies. -/
def fermionCubeMajorana (r : Fin 3) (a : Fin m × Bool) :
    H3 (Qm m) →ₗ[ℂ] H3 (Qm m) := ![maj3₁ a, maj3₂ a, maj3₃ a] r

private lemma middle_swap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a b c d : Module.End ℂ V) (h : b * c = c * b) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  simp only [mul_assoc]
  rw [← mul_assoc b c d, h, mul_assoc]

private lemma slots_mul (A B C D E F : H ι →ₗ[ℂ] H ι) :
    (op1 A * op2 B * op3 C) * (op1 D * op2 E * op3 F) =
      op1 (A * D) * op2 (B * E) * op3 (C * F) := by
  have h31 : op3 C * op1 D = op1 D * op3 C := (op1_op3_comm D C).symm
  have h32 : op3 C * op2 E = op2 E * op3 C := (op2_op3_comm E C).symm
  have h21 : op2 B * op1 D = op1 D * op2 B := (op1_op2_comm D B).symm
  have hc : op3 C * (op1 D * op2 E) = (op1 D * op2 E) * op3 C := by
    rw [← mul_assoc, h31, mul_assoc, h32, ← mul_assoc]
  rw [middle_swap (op1 A * op2 B) (op3 C) (op1 D * op2 E) (op3 F) hc,
    middle_swap (op1 A) (op2 B) (op1 D) (op2 E) h21]
  rw [show op1 A * op1 D = op1 (A * D) from op1_comp A D,
      show op2 B * op2 E = op2 (B * E) from op2_comp B E,
      show op3 C * op3 F = op3 (C * F) from op3_comp C F]

private lemma maj3_forms (a : Fin m × Bool) :
    maj3₁ a = op1 (maj a) * op2 LinearMap.id * op3 LinearMap.id ∧
    maj3₂ a = op1 parityOp * op2 (maj a) * op3 LinearMap.id ∧
    maj3₃ a = op1 parityOp * op2 parityOp * op3 (maj a) := by
  simp only [op2_id, op3_id, Module.End.mul_eq_comp, LinearMap.comp_id]
  exact ⟨rfl, rfl, rfl⟩

private lemma parity_maj_neg (a : Fin m × Bool) :
    maj a * parityOp = -(parityOp * maj a) :=
  eq_neg_of_add_eq_zero_left (add_comm _ _ |>.trans (parityOp_anticomm_maj a))

private lemma maj_neg {a b : Fin m × Bool} (h : a ≠ b) :
    maj a * maj b = -(maj b * maj a) :=
  eq_neg_of_add_eq_zero_left (maj_anticomm h)

lemma maj3_sq (a : Fin m × Bool) :
    maj3₁ a * maj3₁ a = 1 ∧ maj3₂ a * maj3₂ a = 1 ∧ maj3₃ a * maj3₃ a = 1 := by
  rcases maj3_forms a with ⟨h1, h2, h3⟩
  simp only [h1, h2, h3]
  simp only [slots_mul]
  simp only [Module.End.mul_eq_comp, maj_sq, parityOp_sq,
    LinearMap.id_comp, op1_id, op2_id, op3_id]
  constructor <;> first | rfl | (constructor <;> rfl)

lemma maj3_cross (a b : Fin m × Bool) :
    maj3₁ a * maj3₂ b = -(maj3₂ b * maj3₁ a) ∧
    maj3₁ a * maj3₃ b = -(maj3₃ b * maj3₁ a) ∧
    maj3₂ a * maj3₃ b = -(maj3₃ b * maj3₂ a) := by
  rcases maj3_forms a with ⟨h1, h2, h3⟩
  rcases maj3_forms b with ⟨h1', h2', h3'⟩
  simp only [h1, h2, h2', h3']
  simp only [slots_mul]
  simp only [Module.End.mul_eq_comp,
    LinearMap.id_comp, LinearMap.comp_id, parityOp_sq, op1_id, op3_id]
  simp only [show ∀ a : Fin m × Bool, maj a ∘ₗ parityOp = -(parityOp ∘ₗ maj a) from parity_maj_neg,
    op1_neg, op2_neg, LinearMap.neg_comp]
  trivial

lemma maj3_same {a b : Fin m × Bool} (h : a ≠ b) :
    maj3₁ a * maj3₁ b = -(maj3₁ b * maj3₁ a) ∧
    maj3₂ a * maj3₂ b = -(maj3₂ b * maj3₂ a) ∧
    maj3₃ a * maj3₃ b = -(maj3₃ b * maj3₃ a) := by
  rcases maj3_forms a with ⟨h1, h2, h3⟩
  rcases maj3_forms b with ⟨h1', h2', h3'⟩
  simp only [h1, h2, h3, h1', h2', h3']
  simp only [slots_mul]
  simp only [maj_neg h,
    op1_neg, op2_neg, op3_neg, neg_mul, mul_neg, Module.End.mul_eq_comp,
    LinearMap.id_comp, parityOp_sq, op1_id, op2_id, op3_id]
  trivial

theorem fermionCubeMajorana_sq (r : Fin 3) (a : Fin m × Bool) :
    fermionCubeMajorana r a * fermionCubeMajorana r a = 1 := by
  fin_cases r
  · exact (maj3_sq a).1
  · exact (maj3_sq a).2.1
  · exact (maj3_sq a).2.2

theorem fermionCubeMajorana_anticomm (r s : Fin 3) (a b : Fin m × Bool)
    (h : (r, a) ≠ (s, b)) :
    fermionCubeMajorana r a * fermionCubeMajorana s b =
      -(fermionCubeMajorana s b * fermionCubeMajorana r a) := by
  have rev {A B : H3 (Qm m) →ₗ[ℂ] H3 (Qm m)} (h : A * B = -(B * A)) :
      B * A = -(A * B) := by simpa using (congrArg Neg.neg h).symm
  fin_cases r <;> fin_cases s
  · exact (maj3_same (by intro hab; exact h (by simp [hab]))).1
  · exact (maj3_cross a b).1
  · exact (maj3_cross a b).2.1
  · exact rev (maj3_cross b a).1
  · exact (maj3_same (by intro hab; exact h (by simp [hab]))).2.1
  · exact (maj3_cross a b).2.2
  · exact rev (maj3_cross b a).2.1
  · exact rev (maj3_cross b a).2.2
  · exact (maj3_same (by intro hab; exact h (by simp [hab]))).2.2

/-! ### The rotation generators `L_ab = i Σ_a c_{a,A} c_{a,B}` -/

/-- `L₁₂ = i Σ_a c_{a,1} c_{a,2}`. -/
def Lgen12 (m : ℕ) : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) :=
  Complex.I • ∑ a : Fin m × Bool, maj3₁ a ∘ₗ maj3₂ a

/-- `L₂₃ = i Σ_a c_{a,2} c_{a,3}`. -/
def Lgen23 (m : ℕ) : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) :=
  Complex.I • ∑ a : Fin m × Bool, maj3₂ a ∘ₗ maj3₃ a

/-- `L₁₃ = i Σ_a c_{a,1} c_{a,3}`. -/
def Lgen13 (m : ℕ) : H3 (Qm m) →ₗ[ℂ] H3 (Qm m) :=
  Complex.I • ∑ a : Fin m × Bool, maj3₁ a ∘ₗ maj3₃ a

/-- `L₁₂ = -i (Π⊗I⊗I) Λ₁₂` — the parity factor relating `L` and `Λ` on copies 1,2. -/
lemma Lgen12_eq (m : ℕ) :
    Lgen12 m = (-Complex.I) • (op1 (parityOp (m := m)) ∘ₗ p12 (lambdaF m)) := by
  classical
  have ha (a : Fin m × Bool) : maj a ∘ₗ parityOp = -(parityOp ∘ₗ maj a) :=
    eq_neg_of_add_eq_zero_left (add_comm _ _ |>.trans (parityOp_anticomm_maj a))
  simp only [Lgen12, lambdaF, p12_sum, ← p12_comp]
  simp only [maj3₁, maj3₂, ← LinearMap.comp_assoc, op1_comp, ha, op1_neg,
    LinearMap.neg_comp, Finset.sum_neg_distrib, smul_neg, neg_smul]
  change -(Complex.I • ∑ a, op1 (parityOp ∘ₗ maj a) ∘ₗ op2 (maj a)) =
    -(Complex.I • (op1 parityOp ∘ₗ ∑ a, op1 (maj a) ∘ₗ op2 (maj a)))
  simp only [← op1_comp, LinearMap.comp_assoc]
  congr 2
  ext f x
  simp [LinearMap.comp_apply, map_sum, LinearMap.sum_apply, WithLp.ofLp_sum,
    Finset.sum_apply]

/-- `L₂₃ = -i (I⊗Π⊗I) Λ₂₃`. -/
lemma Lgen23_eq (m : ℕ) :
    Lgen23 m = (-Complex.I) • (op2 (parityOp (m := m)) ∘ₗ p23 (lambdaF m)) := by
  classical
  have ht (a : Fin m × Bool) : maj3₂ a * maj3₃ a = -(op2 parityOp * (op2 (maj a) * op3 (maj a))) := by
    rcases maj3_forms a with ⟨h1, h2, h3⟩
    rw [h2, h3]
    have hp : op2 (parityOp (m := m)) = op1 LinearMap.id * op2 parityOp * op3 LinearMap.id := by
      simp [op1_id, op3_id, Module.End.mul_eq_comp]
    have hm : op2 (maj a) * op3 (maj a) =
        op1 LinearMap.id * op2 (maj a) * op3 (maj a) := by
      simp [op1_id, Module.End.mul_eq_comp]
    conv_rhs => rw [hp, hm]
    simp only [slots_mul]
    simp only [Module.End.mul_eq_comp, LinearMap.id_comp, LinearMap.comp_id,
      parityOp_sq, op1_id,
      show maj a ∘ₗ parityOp = -(parityOp ∘ₗ maj a) from parity_maj_neg a,
      op2_neg, LinearMap.neg_comp]
  have he : p23 (lambdaF m) = ∑ a : Fin m × Bool, op2 (maj a) * op3 (maj a) := by
    simp only [lambdaF, p23_sum, ← p23_comp]
    simp only [← op2_eq_p23, op3, Module.End.mul_eq_comp]
  rw [he]
  change Complex.I • (∑ a : Fin m × Bool, maj3₂ a * maj3₃ a) =
    (-Complex.I) • ((op2 parityOp) * (∑ a : Fin m × Bool, op2 (maj a) * op3 (maj a)))
  simp only [ht, Finset.sum_neg_distrib, smul_neg, neg_smul]
  congr 2
  change ∑ a : Fin m × Bool, (op2 parityOp) * (op2 (maj a) * op3 (maj a)) =
    (op2 parityOp) * (∑ a : Fin m × Bool, op2 (maj a) * op3 (maj a))
  rw [Finset.mul_sum]

/-- `L₁₃ = -i (Π⊗Π⊗I) Λ₁₃`. -/
lemma Lgen13_eq (m : ℕ) :
    Lgen13 m = (-Complex.I) •
      (op1 (parityOp (m := m)) ∘ₗ op2 (parityOp (m := m)) ∘ₗ p13 (lambdaF m)) := by
  classical
  have ht (a : Fin m × Bool) : maj3₁ a * maj3₃ a = -(op1 parityOp * op2 parityOp * (op1 (maj a) * op3 (maj a))) := by
    rcases maj3_forms a with ⟨h1, h2, h3⟩
    rw [h1, h3]
    have hp : op1 (parityOp (m := m)) * op2 parityOp =
        op1 parityOp * op2 parityOp * op3 LinearMap.id := by
      rw [op3_id]; rfl
    have hm : op1 (maj a) * op3 (maj a) =
        op1 (maj a) * op2 LinearMap.id * op3 (maj a) := by
      rw [op2_id]; rfl
    conv_rhs => rw [hp, hm]
    simp only [slots_mul]
    simp only [Module.End.mul_eq_comp, LinearMap.id_comp, LinearMap.comp_id,
      show maj a ∘ₗ parityOp = -(parityOp ∘ₗ maj a) from parity_maj_neg a,
      op1_neg, LinearMap.neg_comp]
  have he : p13 (lambdaF m) = ∑ a : Fin m × Bool, op1 (maj a) * op3 (maj a) := by
    simp only [lambdaF, p13_sum, ← p13_comp]
    simp only [← op1_eq_p13, ← op3_eq_p13, Module.End.mul_eq_comp]
  rw [he]
  change Complex.I • (∑ a : Fin m × Bool, maj3₁ a * maj3₃ a) =
    (-Complex.I) • ((op1 parityOp * op2 parityOp) * (∑ a : Fin m × Bool, op1 (maj a) * op3 (maj a)))
  simp only [ht, Finset.sum_neg_distrib, smul_neg, neg_smul]
  congr 2
  change ∑ a : Fin m × Bool, (op1 parityOp * op2 parityOp) * (op1 (maj a) * op3 (maj a)) =
    (op1 parityOp * op2 parityOp) * (∑ a : Fin m × Bool, op1 (maj a) * op3 (maj a))
  rw [Finset.mul_sum]

private lemma ker_involution_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    (U T : Module.End ℂ V) (hU : U * U = 1) : LinearMap.ker (U * T) = LinearMap.ker T := by
  ext f
  simp only [LinearMap.mem_ker, Module.End.mul_apply]
  constructor
  · intro h
    have hh := congrArg U h
    simpa only [← Module.End.mul_apply, ← mul_assoc, hU, one_mul, Module.End.one_apply, map_zero] using hh
  · intro h
    rw [h, map_zero]

/-- The parity factors are invertible, so the kernels agree with those of `Λ_ab`. -/
lemma ker_Lgen12 (m : ℕ) : LinearMap.ker (Lgen12 m) = LinearMap.ker (p12 (lambdaF m)) := by
  rw [Lgen12_eq, LinearMap.ker_smul _ (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)]
  apply ker_involution_comp
  change op1 (parityOp (m := m)) ∘ₗ op1 (parityOp (m := m)) = LinearMap.id
  rw [op1_comp, parityOp_sq, op1_id]

lemma ker_Lgen23 (m : ℕ) : LinearMap.ker (Lgen23 m) = LinearMap.ker (p23 (lambdaF m)) := by
  rw [Lgen23_eq, LinearMap.ker_smul _ (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)]
  apply ker_involution_comp
  change op2 (parityOp (m := m)) ∘ₗ op2 (parityOp (m := m)) = LinearMap.id
  rw [op2_comp, parityOp_sq, op2_id]

lemma ker_Lgen13 (m : ℕ) : LinearMap.ker (Lgen13 m) = LinearMap.ker (p13 (lambdaF m)) := by
  rw [Lgen13_eq, LinearMap.ker_smul _ (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)]
  rw [← LinearMap.comp_assoc]
  apply ker_involution_comp
  change (op1 (parityOp (m := m)) * op2 parityOp) *
    (op1 parityOp * op2 parityOp) = 1
  rw [middle_swap _ _ _ _ (op1_op2_comm _ _).symm]
  change (op1 parityOp ∘ₗ op1 parityOp) ∘ₗ (op2 parityOp ∘ₗ op2 parityOp) = LinearMap.id
  rw [op1_comp, op2_comp, parityOp_sq, op1_id, op2_id, LinearMap.id_comp]

/-! ### The angular-momentum triple -/

private lemma symmetric_comp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A B : Module.End ℂ V} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (h : A * B = B * A) : (A * B).IsSymmetric := by
  intro f g
  change inner ℂ (A (B f)) g = inner ℂ f (A (B g))
  rw [hA, hB]
  exact congrArg (inner ℂ f) (LinearMap.congr_fun h.symm g)

private lemma parity_symmetric : (parityOp (m := m)).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, parityOp_apply, RCLike.inner_apply, map_mul,
    map_pow, map_neg, map_one]
  apply Finset.sum_congr rfl
  intro x _
  ring

private lemma maj3_symmetric (a : Fin m × Bool) :
    (maj3₁ a).IsSymmetric ∧ (maj3₂ a).IsSymmetric ∧ (maj3₃ a).IsSymmetric := by
  refine ⟨op1_isSymmetric (maj_isSymmetric a), ?_, ?_⟩
  · exact symmetric_comp (op1_isSymmetric parity_symmetric)
      (op2_isSymmetric (maj_isSymmetric a)) (op1_op2_comm _ _)
  · apply symmetric_comp
      (symmetric_comp (op1_isSymmetric parity_symmetric) (op2_isSymmetric parity_symmetric)
        (op1_op2_comm _ _)) (op3_isSymmetric (maj_isSymmetric a))
    change (op1 parityOp * op2 parityOp) * op3 (maj a) =
      op3 (maj a) * (op1 parityOp * op2 parityOp)
    rw [mul_assoc, show op2 parityOp * op3 (maj a) = op3 (maj a) * op2 parityOp
      from op2_op3_comm _ _, ← mul_assoc,
      show op1 parityOp * op3 (maj a) = op3 (maj a) * op1 parityOp
      from op1_op3_comm _ _, mul_assoc]

private lemma symmetric_I_mul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A B : Module.End ℂ V} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (h : A * B = -(B * A)) : (Complex.I • (A * B)).IsSymmetric := by
  intro f g
  change inner ℂ (Complex.I • A (B f)) g = inner ℂ f (Complex.I • A (B g))
  rw [inner_smul_left, inner_smul_right, hA, hB, Complex.conj_I]
  have hh : B (A g) = -(A (B g)) := by
    have he := LinearMap.congr_fun h g
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, neg_neg] using (congrArg Neg.neg he).symm
  rw [hh, inner_neg_right]
  ring

/-- The three halved generators are Hermitian. -/
lemma Lgen12_isSymmetric (m : ℕ) : (Lgen12 m).IsSymmetric := by
  classical
  rw [Lgen12, Finset.smul_sum]
  apply LinearMap.isSymmetric_sum
  intro a _
  exact symmetric_I_mul (maj3_symmetric a).1
    (maj3_symmetric a).2.1 (maj3_cross a a).1

lemma Lgen23_isSymmetric (m : ℕ) : (Lgen23 m).IsSymmetric := by
  classical
  rw [Lgen23, Finset.smul_sum]
  apply LinearMap.isSymmetric_sum
  intro a _
  exact symmetric_I_mul (maj3_symmetric a).2.1
    (maj3_symmetric a).2.2 (maj3_cross a a).2.2

lemma Lgen13_isSymmetric (m : ℕ) : (Lgen13 m).IsSymmetric := by
  classical
  rw [Lgen13, Finset.smul_sum]
  apply LinearMap.isSymmetric_sum
  intro a _
  exact symmetric_I_mul (maj3_symmetric a).1
    (maj3_symmetric a).2.2 (maj3_cross a a).2.1

private lemma anticomm_reverse {R : Type*} [Ring R] {u v : R}
    (h : u * v = -(v * u)) : v * u = -(u * v) := by
  simpa using (congrArg Neg.neg h).symm

private lemma anticomm_mul_comm {R : Type*} [Ring R] (u v w : R)
    (hv : u * v = -(v * u)) (hw : u * w = -(w * u)) : Commute u (v * w) := by
  change u * (v * w) = (v * w) * u
  rw [← mul_assoc, hv, neg_mul, mul_assoc, hw, mul_neg, neg_neg, ← mul_assoc]

private lemma bivector_disjoint {V : Type*} [AddCommGroup V] [Module ℂ V]
    (u v w x : Module.End ℂ V)
    (huw : u * w = -(w * u)) (hux : u * x = -(x * u))
    (hvw : v * w = -(w * v)) (hvx : v * x = -(x * v)) :
    ⁅u * v, w * x⁆ = 0 := by
  rw [Ring.lie_def, ((anticomm_mul_comm u w x huw hux).mul_left
    (anticomm_mul_comm v w x hvw hvx)).eq, sub_self]

private lemma bivector_adjacent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (u v w : Module.End ℂ V) (hv : v * v = 1)
    (huv : u * v = -(v * u)) (huw : u * w = -(w * u))
    (hvw : v * w = -(w * v)) : ⁅u * v, v * w⁆ = (2 : ℂ) • (u * w) := by
  have hf : (u * v) * (v * w) = u * w := by
    rw [mul_assoc, ← mul_assoc v v w, hv, one_mul]
  have hr : (v * w) * (u * v) = -(u * w) := by
    rw [mul_assoc, ← mul_assoc w u v, anticomm_reverse huw, neg_mul, mul_neg,
      mul_assoc, ← mul_assoc v u (w * v), anticomm_reverse huv, neg_mul,
      neg_neg, mul_assoc, ← mul_assoc v w v, hvw, neg_mul, mul_neg, mul_assoc w v v, hv, mul_one]
  rw [Ring.lie_def, hf, hr, sub_neg_eq_add, two_smul ℂ]

private lemma bivector_other {V : Type*} [AddCommGroup V] [Module ℂ V]
    (u v w : Module.End ℂ V) (hu : u * u = 1) (_hv : v * v = 1) (hw : w * w = 1)
    (huv : u * v = -(v * u)) (huw : u * w = -(w * u))
    (hvw : v * w = -(w * v)) :
    ⁅v * w, u * w⁆ = (2 : ℂ) • (u * v) ∧
    ⁅u * w, u * v⁆ = (2 : ℂ) • (v * w) := by
  constructor
  · have h := bivector_adjacent v w u hw hvw (anticomm_reverse huv) (anticomm_reverse huw)
    rw [anticomm_reverse huw, show ∀ A B : Module.End ℂ V, ⁅A, -B⁆ = -⁅A, B⁆ by
      intros; simp [Ring.lie_def]; abel, anticomm_reverse huv, smul_neg] at h
    exact neg_injective h
  · have h := bivector_adjacent w u v hu (anticomm_reverse huw) (anticomm_reverse hvw) huv
    rw [anticomm_reverse huw, show ∀ A B : Module.End ℂ V, ⁅-A, B⁆ = -⁅A, B⁆ by
      intros; simp [Ring.lie_def]; abel, anticomm_reverse hvw, smul_neg] at h
    exact neg_injective h

private lemma bracket_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c d : ℂ) (A B : Module.End ℂ V) :
    ⁅c • A, d • B⁆ = (c * d) • ⁅A, B⁆ := by
  simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]
  rw [mul_comm d c]

private lemma bracket_sum {V κ : Type*} [AddCommGroup V] [Module ℂ V] [Fintype κ]
    (A B : κ → Module.End ℂ V) :
    ⁅∑ a, A a, ∑ b, B b⁆ = ∑ a, ∑ b, ⁅A a, B b⁆ := by
  simp only [Ring.lie_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

private lemma bracket_sum_diagonal {V κ : Type*} [AddCommGroup V] [Module ℂ V] [Fintype κ]
    (A B C : κ → Module.End ℂ V)
    (hd : ∀ a, ⁅A a, B a⁆ = (2 : ℂ) • C a)
    (ho : ∀ a b, a ≠ b → ⁅A a, B b⁆ = 0) :
    ⁅Complex.I • ∑ a, A a, Complex.I • ∑ b, B b⁆ =
      (2 * Complex.I) • (Complex.I • ∑ a, C a) := by
  classical
  rw [bracket_smul, Complex.I_mul_I, bracket_sum]
  have hh (a : κ) : ∑ b, ⁅A a, B b⁆ = (2 : ℂ) • C a := by
    rw [Finset.sum_eq_single a]
    · exact hd a
    · intro b _ hb
      exact ho a b hb.symm
    · simp
  simp only [hh, ← Finset.smul_sum, smul_smul]
  congr 1
  simp [mul_assoc, Complex.I_mul_I]

/-- `[L₁₂, L₂₃] = 2i L₁₃` (per-mode CAR computation; cross terms vanish). -/
lemma commutator_L12_L23 (m : ℕ) :
    ⁅Lgen12 m, Lgen23 m⁆ = (2 * Complex.I) • Lgen13 m := by
  classical
  unfold Lgen12 Lgen23 Lgen13
  apply bracket_sum_diagonal
  · intro a
    exact bivector_adjacent _ _ _ (maj3_sq a).2.1
      (maj3_cross a a).1 (maj3_cross a a).2.1 (maj3_cross a a).2.2
  · intro a b hab
    apply bivector_disjoint
    · exact (maj3_cross a b).1
    · exact (maj3_cross a b).2.1
    · exact (maj3_same hab).2.1
    · exact (maj3_cross a b).2.2

/-- `[L₂₃, L₁₃] = 2i L₁₂`. -/
lemma commutator_L23_L13 (m : ℕ) :
    ⁅Lgen23 m, Lgen13 m⁆ = (2 * Complex.I) • Lgen12 m := by
  classical
  unfold Lgen23 Lgen13 Lgen12
  apply bracket_sum_diagonal
  · intro a
    exact (bivector_other _ _ _ (maj3_sq a).1 (maj3_sq a).2.1 (maj3_sq a).2.2
      (maj3_cross a a).1 (maj3_cross a a).2.1 (maj3_cross a a).2.2).1
  · intro a b hab
    apply bivector_disjoint
    · exact anticomm_reverse (maj3_cross b a).1
    · exact (maj3_cross a b).2.2
    · exact anticomm_reverse (maj3_cross b a).2.1
    · exact (maj3_same hab).2.2

/-- `[L₁₃, L₁₂] = 2i L₂₃`. -/
lemma commutator_L13_L12 (m : ℕ) :
    ⁅Lgen13 m, Lgen12 m⁆ = (2 * Complex.I) • Lgen23 m := by
  classical
  unfold Lgen13 Lgen12 Lgen23
  apply bracket_sum_diagonal
  · intro a
    exact (bivector_other _ _ _ (maj3_sq a).1 (maj3_sq a).2.1 (maj3_sq a).2.2
      (maj3_cross a a).1 (maj3_cross a a).2.1 (maj3_cross a a).2.2).2
  · intro a b hab
    apply bivector_disjoint
    · exact (maj3_same hab).1
    · exact (maj3_cross a b).1
    · exact anticomm_reverse (maj3_cross b a).2.1
    · exact anticomm_reverse (maj3_cross b a).2.2

/-- The fermionic angular momentum triple `(Jx, Jy, Jz) = (L₁₂, L₂₃, L₁₃)/2` on the
three-copy Fock space. -/
def fermionJ (m : ℕ) : AngularMomentum (H3 (Qm m)) where
  Jx := (2 : ℂ)⁻¹ • Lgen12 m
  Jy := (2 : ℂ)⁻¹ • Lgen23 m
  Jz := (2 : ℂ)⁻¹ • Lgen13 m
  hJx := by
    exact (Lgen12_isSymmetric m).smul (by simp only [map_inv₀, map_ofNat])
  hJy := by
    exact (Lgen23_isSymmetric m).smul (by simp only [map_inv₀, map_ofNat])
  hJz := by
    exact (Lgen13_isSymmetric m).smul (by simp only [map_inv₀, map_ofNat])
  comm_xy := by
    rw [bracket_smul, commutator_L12_L23, smul_smul, smul_smul]
    congr 1
    norm_num
    ring
  comm_yz := by
    rw [bracket_smul, commutator_L23_L13, smul_smul, smul_smul]
    congr 1
    norm_num
    ring
  comm_zx := by
    rw [bracket_smul, commutator_L13_L12, smul_smul, smul_smul]
    congr 1
    norm_num
    ring

/-! ### `P_ab` is the projection onto `ker Λ_ab`, and `S = T_π` -/

omit [Fintype ι] in
private lemma slice3_zero [Fintype ι] (k : ι) : slice3 k (0 : H3 ι) = 0 := rfl

omit [Fintype ι] in
private lemma slice3_sub [Fintype ι] (k : ι) (f g : H3 ι) :
    slice3 k (f - g) = slice3 k f - slice3 k g := rfl

omit [Fintype ι] in
private lemma p12_ker_slices [Fintype ι] (A : H2 ι →ₗ[ℂ] H2 ι) (f : H3 ι) :
    f ∈ LinearMap.ker (p12 A) ↔ ∀ k, slice3 k f ∈ LinearMap.ker A := by
  constructor
  · intro hf k
    have h := congrArg (slice3 k) (LinearMap.mem_ker.mp hf)
    simpa only [slice3_p12, slice3_zero, LinearMap.mem_ker] using h
  · intro hf
    apply LinearMap.mem_ker.mpr
    ext p
    exact congrArg (fun v : H2 ι => v (p.1, p.2.1)) (LinearMap.mem_ker.mp (hf p.2.2))

omit [Fintype ι] in
private lemma slice1_zero [Fintype ι] (k : ι) : slice1 k (0 : H3 ι) = 0 := rfl

omit [Fintype ι] in
private lemma slice1_sub [Fintype ι] (k : ι) (f g : H3 ι) :
    slice1 k (f - g) = slice1 k f - slice1 k g := rfl

omit [Fintype ι] in
private lemma p23_ker_slices [Fintype ι] (A : H2 ι →ₗ[ℂ] H2 ι) (f : H3 ι) :
    f ∈ LinearMap.ker (p23 A) ↔ ∀ k, slice1 k f ∈ LinearMap.ker A := by
  constructor
  · intro hf k
    have h := congrArg (slice1 k) (LinearMap.mem_ker.mp hf)
    simpa only [slice1_p23, slice1_zero, LinearMap.mem_ker] using h
  · intro hf
    apply LinearMap.mem_ker.mpr
    ext p
    exact congrArg (fun v : H2 ι => v (p.2.1, p.2.2)) (LinearMap.mem_ker.mp (hf p.1))

omit [Fintype ι] in
private lemma slice2_zero [Fintype ι] (k : ι) : slice2 k (0 : H3 ι) = 0 := rfl

omit [Fintype ι] in
private lemma slice2_sub [Fintype ι] (k : ι) (f g : H3 ι) :
    slice2 k (f - g) = slice2 k f - slice2 k g := rfl

omit [Fintype ι] in
private lemma p13_ker_slices [Fintype ι] (A : H2 ι →ₗ[ℂ] H2 ι) (f : H3 ι) :
    f ∈ LinearMap.ker (p13 A) ↔ ∀ k, slice2 k f ∈ LinearMap.ker A := by
  constructor
  · intro hf k
    have h := congrArg (slice2 k) (LinearMap.mem_ker.mp hf)
    simpa only [slice2_p13, slice2_zero, LinearMap.mem_ker] using h
  · intro hf
    apply LinearMap.mem_ker.mpr
    ext p
    exact congrArg (fun v : H2 ι => v (p.1, p.2.2)) (LinearMap.mem_ker.mp (hf p.2.1))

/-- Embedded kernel projections: `p12 (PF) = starProjection (ker Λ₁₂)` (and cyclically).
Proof: `p12 (PF) f` has slices `PF (slice f) ∈ ker Λ`, so `Λ₁₂ (p12 PF f) = 0`; and
`f - p12 PF f` has slices orthogonal to `ker Λ`, hence is orthogonal to `ker Λ₁₂`
(whose elements have all slices in `ker Λ`); conclude by uniqueness of the orthogonal
decomposition. -/
lemma p12_PF (m : ℕ) :
    p12 (PF m) = ((LinearMap.ker (p12 (lambdaF m))).starProjection :
      H3 (Qm m) →L[ℂ] H3 (Qm m)) := by
  classical
  apply LinearMap.ext
  intro f
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [p12_ker_slices]
    intro k
    rw [slice3_p12]
    exact (LinearMap.ker (lambdaF m)).starProjection_apply_mem _
  · intro g hg
    rw [inner_eq_sum_slice3]
    apply Finset.sum_eq_zero
    intro k _
    rw [slice3_sub, slice3_p12]
    exact (LinearMap.ker (lambdaF m)).starProjection_inner_eq_zero _ _
      ((p12_ker_slices _ _).mp hg k)

lemma p23_PF (m : ℕ) :
    p23 (PF m) = ((LinearMap.ker (p23 (lambdaF m))).starProjection :
      H3 (Qm m) →L[ℂ] H3 (Qm m)) := by
  classical
  apply LinearMap.ext
  intro f
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [p23_ker_slices]
    intro k
    rw [slice1_p23]
    exact (LinearMap.ker (lambdaF m)).starProjection_apply_mem _
  · intro g hg
    rw [inner_eq_sum_slice1]
    apply Finset.sum_eq_zero
    intro k _
    rw [slice1_sub, slice1_p23]
    exact (LinearMap.ker (lambdaF m)).starProjection_inner_eq_zero _ _
      ((p23_ker_slices _ _).mp hg k)

lemma p13_PF (m : ℕ) :
    p13 (PF m) = ((LinearMap.ker (p13 (lambdaF m))).starProjection :
      H3 (Qm m) →L[ℂ] H3 (Qm m)) := by
  classical
  apply LinearMap.ext
  intro f
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [p13_ker_slices]
    intro k
    rw [slice2_p13]
    exact (LinearMap.ker (lambdaF m)).starProjection_apply_mem _
  · intro g hg
    rw [inner_eq_sum_slice2]
    apply Finset.sum_eq_zero
    intro k _
    rw [slice2_sub, slice2_p13]
    exact (LinearMap.ker (lambdaF m)).starProjection_inner_eq_zero _ _
      ((p13_ker_slices _ _).mp hg k)

/-- The three-copy symmetrized operator of the fermionic test is the Kac operator of
the fermionic angular-momentum triple. -/
theorem Sop_PF_eq_kacT (m : ℕ) : Sop (PF m) = kacT (fermionJ m) := by
  have hx : LinearMap.ker (fermionJ m).Jx = LinearMap.ker (p12 (lambdaF m)) := by
    rw [fermionJ, LinearMap.ker_smul _ _ (inv_ne_zero (by norm_num)), ker_Lgen12]
  have hy : LinearMap.ker (fermionJ m).Jy = LinearMap.ker (p23 (lambdaF m)) := by
    rw [fermionJ, LinearMap.ker_smul _ _ (inv_ne_zero (by norm_num)), ker_Lgen23]
  have hz : LinearMap.ker (fermionJ m).Jz = LinearMap.ker (p13 (lambdaF m)) := by
    rw [fermionJ, LinearMap.ker_smul _ _ (inv_ne_zero (by norm_num)), ker_Lgen13]
  simp only [Sop, kacT, hx, hy, hz, p12_PF, p23_PF, p13_PF,
    ContinuousLinearMap.toLinearMap_add]
  congr 1
  abel

end

end GaussianTesting
