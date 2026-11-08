module

/-
Finite-dimensional model of Lemma 3.2 (`lem:three-copy-moments`): the first and second moments of the
three-copy operator `S = (P₁₂+P₁₃+P₂₃)/3` in the state `ψ⊗ψ⊗ψ` compute the acceptance
probability `p(ψ)` and the second moment `q(ψ) = ‖K_ψ ψ‖²`:

    ⟨S⟩_{ψ⊗3} = p(ψ)   and   ⟨S²⟩_{ψ⊗3} = (p(ψ) + 2 q(ψ))/3.

The proof decomposes the three-copy inner product into slices. Idempotence
gives the diagonal terms of the second moment. Swap invariance makes the
coefficient matrix `M(i,j) = (P ψ⊗ψ)(i,j)` symmetric, giving the cross terms.
-/
public import GaussianTesting.GradientFlow.Defs

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {ι : Type*} [fintypeι : Fintype ι]

/-! ### Slice decompositions of `H^⊗3`

`slice3 k f` is the two-copy vector obtained from `f` by fixing the third index to `k`
(and similarly `slice1`, `slice2` for the first and second index). The inner product on
`H^⊗3` decomposes as a sum of two-copy inner products over slices, and each `P_{ab}`
acts as `P` on the matching slices. -/

/-- Fix the third coordinate. -/
def slice3 (k : ι) (f : H3 ι) : H2 ι := WithLp.toLp 2 fun q => f (q.1, q.2, k)

/-- Fix the first coordinate. -/
def slice1 (i : ι) (f : H3 ι) : H2 ι := WithLp.toLp 2 fun q => f (i, q.1, q.2)

/-- Fix the second coordinate. -/
def slice2 (j : ι) (f : H3 ι) : H2 ι := WithLp.toLp 2 fun q => f (q.1, j, q.2)

omit fintypeι in
@[simp] lemma slice3_apply [Fintype ι] (k : ι) (f : H3 ι) (q : ι × ι) :
    slice3 k f q = f (q.1, q.2, k) := rfl

omit fintypeι in
@[simp] lemma slice1_apply [Fintype ι] (i : ι) (f : H3 ι) (q : ι × ι) :
    slice1 i f q = f (i, q.1, q.2) := rfl

omit fintypeι in
@[simp] lemma slice2_apply [Fintype ι] (j : ι) (f : H3 ι) (q : ι × ι) :
    slice2 j f q = f (q.1, j, q.2) := rfl

lemma inner_eq_sum_slice3 (f g : H3 ι) :
    ⟪f, g⟫_ℂ = ∑ k, ⟪slice3 k f, slice3 k g⟫_ℂ := by
  simp only [PiLp.inner_apply, slice3_apply, Fintype.sum_prod_type]
  simp_rw [Finset.sum_comm (s := (univ : Finset ι)) (t := (univ : Finset ι)) (f := fun j k => ⟪f (_, j, k), g (_, j, k)⟫_ℂ)]
  rw [Finset.sum_comm]

lemma inner_eq_sum_slice1 (f g : H3 ι) :
    ⟪f, g⟫_ℂ = ∑ i, ⟪slice1 i f, slice1 i g⟫_ℂ := by
  simp only [PiLp.inner_apply, slice1_apply, Fintype.sum_prod_type]

lemma inner_eq_sum_slice2 (f g : H3 ι) :
    ⟪f, g⟫_ℂ = ∑ j, ⟪slice2 j f, slice2 j g⟫_ℂ := by
  simp only [PiLp.inner_apply, slice2_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit fintypeι in
/-- `P₁₂` acts as `P` on third-coordinate slices (definitional). -/
lemma slice3_p12 [Fintype ι] (P : H2 ι →ₗ[ℂ] H2 ι) (k : ι) (f : H3 ι) :
    slice3 k (p12 P f) = P (slice3 k f) := rfl

omit fintypeι in
/-- `P₂₃` acts as `P` on first-coordinate slices (definitional). -/
lemma slice1_p23 [Fintype ι] (P : H2 ι →ₗ[ℂ] H2 ι) (i : ι) (f : H3 ι) :
    slice1 i (p23 P f) = P (slice1 i f) := rfl

omit fintypeι in
/-- `P₁₃` acts as `P` on second-coordinate slices (definitional). -/
lemma slice2_p13 [Fintype ι] (P : H2 ι →ₗ[ℂ] H2 ι) (j : ι) (f : H3 ι) :
    slice2 j (p13 P f) = P (slice2 j f) := rfl

/-! ### Symmetry and idempotence of the `P_{ab}` -/

variable {P : H2 ι →ₗ[ℂ] H2 ι}

lemma p12_isSymmetric (hP : P.IsSymmetric) : (p12 P).IsSymmetric := by
  intro f g
  simp only [inner_eq_sum_slice3, slice3_p12]
  exact Finset.sum_congr rfl (fun i _ => hP _ _)

lemma p23_isSymmetric (hP : P.IsSymmetric) : (p23 P).IsSymmetric := by
  intro f g
  simp only [inner_eq_sum_slice1, slice1_p23]
  exact Finset.sum_congr rfl (fun i _ => hP _ _)

lemma p13_isSymmetric (hP : P.IsSymmetric) : (p13 P).IsSymmetric := by
  intro f g
  simp only [inner_eq_sum_slice2, slice2_p13]
  exact Finset.sum_congr rfl (fun i _ => hP _ _)

omit fintypeι in
/-- `p12` is multiplicative (hence sends idempotents to idempotents). -/
lemma p12_comp [Fintype ι] (P Q : H2 ι →ₗ[ℂ] H2 ι) : p12 P ∘ₗ p12 Q = p12 (P ∘ₗ Q) := by
  rfl

omit fintypeι in
lemma p23_comp [Fintype ι] (P Q : H2 ι →ₗ[ℂ] H2 ι) : p23 P ∘ₗ p23 Q = p23 (P ∘ₗ Q) := by
  rfl

omit fintypeι in
lemma p13_comp [Fintype ι] (P Q : H2 ι →ₗ[ℂ] H2 ι) : p13 P ∘ₗ p13 Q = p13 (P ∘ₗ Q) := by
  rfl

/-! ### Reality of the two scalar moments -/

/-- For symmetric `P` the acceptance inner product is real, and equals `accProb`. -/
lemma inner_tp2_P_self (hP : P.IsSymmetric) (ψ : H ι) :
    ⟪tp2 ψ ψ, P (tp2 ψ ψ)⟫_ℂ = (accProb P ψ : ℂ) := by
  unfold accProb
  apply Eq.symm
  apply Complex.conj_eq_iff_re.mp
  rw [inner_conj_symm]
  exact hP _ _

/-- The inner product of `Kvec` with itself is real, and equals `qProb`. -/
lemma inner_Kvec_self (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) :
    ⟪Kvec P ψ, Kvec P ψ⟫_ℂ = (qProb P ψ : ℂ) := by
  unfold qProb
  exact (Complex.conj_eq_iff_re.mp (inner_conj_symm _ _)).symm

/-! ### The matrix `M(i,j) = (P ψ⊗ψ)(i,j)` is symmetric -/

/-- Swap-invariance of `P` makes `P (ψ⊗ψ)` a symmetric "matrix". -/
lemma P_tp2_self_symm (hP : IsAcceptanceProjection P) (ψ : H ι) (i j : ι) :
    P (tp2 ψ ψ) (i, j) = P (tp2 ψ ψ) (j, i) := by
  have h := hP.swap_comm (tp2 ψ ψ)
  rw [swap2_tp2] at h
  exact congrArg (fun f : H2 ι => f (i, j)) h

/-! ### First moments: `⟨ψ⊗³, P_{ab} ψ⊗³⟩ = ⟨ψ⊗ψ, P ψ⊗ψ⟩ ⟨ψ,ψ⟩` -/

lemma inner_tp3_p12_tp3 (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) :
    ⟪tp3 ψ ψ ψ, p12 P (tp3 ψ ψ ψ)⟫_ℂ = ⟪tp2 ψ ψ, P (tp2 ψ ψ)⟫_ℂ * ⟪ψ, ψ⟫_ℂ := by
  rw [p12_tp3]
  simp only [PiLp.inner_apply, RCLike.inner_apply, tp3_apply, tp2_apply,
    Fintype.sum_prod_type, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    intro i
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma inner_tp3_p23_tp3 (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) :
    ⟪tp3 ψ ψ ψ, p23 P (tp3 ψ ψ ψ)⟫_ℂ = ⟪tp2 ψ ψ, P (tp2 ψ ψ)⟫_ℂ * ⟪ψ, ψ⟫_ℂ := by
  rw [p23_tp3]
  simp only [PiLp.inner_apply, RCLike.inner_apply, tp3_apply, tp2_apply,
    Fintype.sum_prod_type, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma inner_tp3_p13_tp3 (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) :
    ⟪tp3 ψ ψ ψ, p13 P (tp3 ψ ψ ψ)⟫_ℂ = ⟪tp2 ψ ψ, P (tp2 ψ ψ)⟫_ℂ * ⟪ψ, ψ⟫_ℂ := by
  rw [p13_tp3]
  simp only [PiLp.inner_apply, RCLike.inner_apply, tp3_apply, tp2_apply,
    Fintype.sum_prod_type, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-! ### Cross terms: `⟨P_{ab} ψ⊗³, P_{cd} ψ⊗³⟩ = ⟨K_ψψ, K_ψψ⟩` for `{a,b} ≠ {c,d}`

Proof sketch (for 12/23; others analogous): with `M(i,j) := (P ψ⊗ψ)(i,j)` and
`K := Kvec P ψ`, we have `(P₁₂ ψ⊗³)(i,j,k) = M(i,j) ψ(k)` and
`(P₂₃ ψ⊗³)(i,j,k) = ψ(i) M(j,k)` (by `p12_tp3`, `p23_tp3`), so the inner product
is `∑ⱼ (∑ᵢ conj(M i j) ψ i) (∑ₖ conj(ψ k) M j k) = ∑ⱼ conj(K j) * (K j)`, using the
symmetry of `M` (`P_tp2_self_symm`) and `conj (∑ᵢ M i j conj (ψ i)) = ∑ᵢ conj(M i j) ψ i`. -/

lemma inner_p12_p23_tp3 (hP : IsAcceptanceProjection P) (ψ : H ι) :
    ⟪p12 P (tp3 ψ ψ ψ), p23 P (tp3 ψ ψ ψ)⟫_ℂ = ⟪Kvec P ψ, Kvec P ψ⟫_ℂ := by
  rw [p12_tp3, p23_tp3]
  simp only [PiLp.inner_apply, RCLike.inner_apply,
    Fintype.sum_prod_type, Kvec_apply, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [P_tp2_self_symm hP ψ j i]
  ring

lemma inner_p12_p13_tp3 (_hP : IsAcceptanceProjection P) (ψ : H ι) :
    ⟪p12 P (tp3 ψ ψ ψ), p13 P (tp3 ψ ψ ψ)⟫_ℂ = ⟪Kvec P ψ, Kvec P ψ⟫_ℂ := by
  rw [p12_tp3, p13_tp3]
  simp only [PiLp.inner_apply, RCLike.inner_apply,
    Fintype.sum_prod_type, Kvec_apply, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma inner_p13_p23_tp3 (hP : IsAcceptanceProjection P) (ψ : H ι) :
    ⟪p13 P (tp3 ψ ψ ψ), p23 P (tp3 ψ ψ ψ)⟫_ℂ = ⟪Kvec P ψ, Kvec P ψ⟫_ℂ := by
  rw [p13_tp3, p23_tp3]
  simp only [PiLp.inner_apply, RCLike.inner_apply,
    Fintype.sum_prod_type, Kvec_apply, map_sum, map_mul, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [P_tp2_self_symm hP ψ j i, P_tp2_self_symm hP ψ k i]
  ring

/-! ### The moments lemma (`lem:three-copy-moments`) -/

/-- First moment: `⟨S⟩_{ψ⊗3} = p(ψ)` for a unit vector `ψ`. -/
theorem inner_tp3_Sop_tp3 (hP : IsAcceptanceProjection P) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    ⟪tp3 ψ ψ ψ, Sop P (tp3 ψ ψ ψ)⟫_ℂ = (accProb P ψ : ℂ) := by
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  simp only [Sop, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_right,
    inner_add_right, inner_tp3_p12_tp3, inner_tp3_p13_tp3, inner_tp3_p23_tp3,
    inner_tp2_P_self hP.symmetric, hn, mul_one]
  ring

/-- Second moment: `⟨S²⟩_{ψ⊗3} = (p(ψ) + 2q(ψ))/3` for a unit vector `ψ`. -/
theorem inner_Sop_Sop_tp3 (hP : IsAcceptanceProjection P) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    ⟪Sop P (tp3 ψ ψ ψ), Sop P (tp3 ψ ψ ψ)⟫_ℂ
      = (((accProb P ψ + 2 * qProb P ψ) / 3 : ℝ) : ℂ) := by
  have hn : ⟪ψ, ψ⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  let x := tp3 ψ ψ ψ
  have hd12 : ⟪p12 P x, p12 P x⟫_ℂ = (accProb P ψ : ℂ) := by
    rw [p12_isSymmetric hP.symmetric]
    have hi : p12 P (p12 P x) = p12 P x := by
      change (p12 P ∘ₗ p12 P) x = _
      rw [p12_comp, hP.idem]
    rw [hi]
    exact (inner_tp3_p12_tp3 P ψ).trans (by rw [inner_tp2_P_self hP.symmetric, hn, mul_one])
  have hd13 : ⟪p13 P x, p13 P x⟫_ℂ = (accProb P ψ : ℂ) := by
    rw [p13_isSymmetric hP.symmetric]
    have hi : p13 P (p13 P x) = p13 P x := by
      change (p13 P ∘ₗ p13 P) x = _
      rw [p13_comp, hP.idem]
    rw [hi]
    exact (inner_tp3_p13_tp3 P ψ).trans (by rw [inner_tp2_P_self hP.symmetric, hn, mul_one])
  have hd23 : ⟪p23 P x, p23 P x⟫_ℂ = (accProb P ψ : ℂ) := by
    rw [p23_isSymmetric hP.symmetric]
    have hi : p23 P (p23 P x) = p23 P x := by
      change (p23 P ∘ₗ p23 P) x = _
      rw [p23_comp, hP.idem]
    rw [hi]
    exact (inner_tp3_p23_tp3 P ψ).trans (by rw [inner_tp2_P_self hP.symmetric, hn, mul_one])
  have hc1213 : ⟪p12 P x, p13 P x⟫_ℂ = (qProb P ψ : ℂ) :=
    (inner_p12_p13_tp3 hP ψ).trans (inner_Kvec_self P ψ)
  have hc1312 : ⟪p13 P x, p12 P x⟫_ℂ = (qProb P ψ : ℂ) := by
    rw [← inner_conj_symm, hc1213, Complex.conj_ofReal]
  have hc1223 : ⟪p12 P x, p23 P x⟫_ℂ = (qProb P ψ : ℂ) :=
    (inner_p12_p23_tp3 hP ψ).trans (inner_Kvec_self P ψ)
  have hc2312 : ⟪p23 P x, p12 P x⟫_ℂ = (qProb P ψ : ℂ) := by
    rw [← inner_conj_symm, hc1223, Complex.conj_ofReal]
  have hc1323 : ⟪p13 P x, p23 P x⟫_ℂ = (qProb P ψ : ℂ) :=
    (inner_p13_p23_tp3 hP ψ).trans (inner_Kvec_self P ψ)
  have hc2313 : ⟪p23 P x, p13 P x⟫_ℂ = (qProb P ψ : ℂ) := by
    rw [← inner_conj_symm, hc1323, Complex.conj_ofReal]
  change ⟪Sop P x, Sop P x⟫_ℂ = _
  simp only [Sop, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left,
    inner_smul_right, inner_add_left, inner_add_right,
    hd12, hd13, hd23, hc1213, hc1312, hc1223, hc2312, hc1323, hc2313]
  push_cast
  simp only [map_inv₀, map_ofNat]
  norm_num
  ring

end

end GaussianTesting
