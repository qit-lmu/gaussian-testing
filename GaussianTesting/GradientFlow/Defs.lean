module

/-
Definitions for Section 3 ("Robustness of property tests from gradient flows") of
"Testing bosonic and fermionic Gaussian states with a constant number of copies"
(Briët, Castro-Silva, Walter, Witteveen).

We work with a concrete finite-dimensional model: the Hilbert space is
`EuclideanSpace ℂ ι` for a finite index type `ι`, and tensor copies are modeled by
product index types (`ι × ι`, `ι × ι × ι`), with elementary tensors given by pointwise
products. The order of the product indices specifies the order of the tensor factors.

Paper correspondence:
* `tp2 ψ φ`    = ψ ⊗ φ, `tp3 ψ φ χ` = ψ ⊗ φ ⊗ χ
* `swap2`      = the swap operator on H ⊗ H
* `IsAcceptanceProjection P` = "orthogonal projection on H^⊗2 commuting with the swap"
* `accProb P ψ` = p(ψ) = ⟨ψ⊗ψ, P ψ⊗ψ⟩                     (eq:p-accept-2-copies)
* `Kvec P ψ`   = K_ψ |ψ⟩ = (I ⊗ ⟨ψ|) P |ψ⟩^⊗2
* `qProb P ψ`  = q(ψ) = ‖K_ψ ψ‖²                           (eq:grad via p and q)
* `p12/p13/p23 P` = P_{ab} acting on copies a,b of H^⊗3
* `Sop P`      = S = (P₁₂ + P₁₃ + P₂₃)/3                   (eq:def-S)
-/
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Symmetric

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

/-- The Hilbert space of the system: `ℂ^ι` with the standard inner product. -/
abbrev H (ι : Type*) : Type _ := EuclideanSpace ℂ ι

/-- Two copies of the system, `H ⊗ H`, modeled on the product index type. -/
abbrev H2 (ι : Type*) : Type _ := EuclideanSpace ℂ (ι × ι)

/-- Three copies of the system, `H ⊗ H ⊗ H`, modeled on the product index type. -/
abbrev H3 (ι : Type*) : Type _ := EuclideanSpace ℂ (ι × ι × ι)

/-! ### Elementary tensors -/

/-- The elementary tensor `ψ ⊗ φ` of two vectors (allowing different index types). -/
def tp2 {ι κ : Type*} (ψ : H ι) (φ : H κ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 fun p => ψ p.1 * φ p.2

/-- The elementary tensor `ψ ⊗ φ ⊗ χ` of three vectors. -/
def tp3 {ι : Type*} (ψ φ χ : H ι) : H3 ι :=
  WithLp.toLp 2 fun p => ψ p.1 * φ p.2.1 * χ p.2.2

@[simp] lemma tp2_apply {ι κ : Type*} (ψ : H ι) (φ : H κ) (p : ι × κ) :
    tp2 ψ φ p = ψ p.1 * φ p.2 := rfl

@[simp] lemma tp3_apply {ι : Type*} (ψ φ χ : H ι) (p : ι × ι × ι) :
    tp3 ψ φ χ p = ψ p.1 * φ p.2.1 * χ p.2.2 := rfl

/-- A triple tensor is an iterated double tensor. -/
lemma tp3_eq_tp2_tp2 {ι : Type*} (ψ φ χ : H ι) : tp3 ψ φ χ = tp2 ψ (tp2 φ χ) := by
  ext p; simp [mul_assoc]

/-- Inner products of elementary tensors factorize. -/
lemma inner_tp2_tp2 {ι κ : Type*} [Fintype ι] [Fintype κ] (ψ ψ' : H ι) (φ φ' : H κ) :
    ⟪tp2 ψ φ, tp2 ψ' φ'⟫_ℂ = ⟪ψ, ψ'⟫_ℂ * ⟪φ, φ'⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, tp2_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp only [map_mul]
  congr 1; ext i; congr 1; ext j; ring

/-- Inner products of elementary triple tensors factorize. -/
lemma inner_tp3_tp3 {ι : Type*} [Fintype ι] (ψ φ χ ψ' φ' χ' : H ι) :
    ⟪tp3 ψ φ χ, tp3 ψ' φ' χ'⟫_ℂ = ⟪ψ, ψ'⟫_ℂ * ⟪φ, φ'⟫_ℂ * ⟪χ, χ'⟫_ℂ := by
  rw [tp3_eq_tp2_tp2, tp3_eq_tp2_tp2, inner_tp2_tp2, inner_tp2_tp2, mul_assoc]

variable {ι : Type*} [fintypeι : Fintype ι]

/-! ### The swap operator on two copies -/

/-- The swap operator `ψ ⊗ φ ↦ φ ⊗ ψ` on `H ⊗ H`, as a linear isometry equivalence. -/
def swap2 : H2 ι ≃ₗᵢ[ℂ] H2 ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodComm ι ι)

@[simp] lemma swap2_apply (f : H2 ι) (p : ι × ι) : swap2 f p = f (p.2, p.1) := rfl

@[simp] lemma swap2_tp2 (ψ φ : H ι) : swap2 (tp2 ψ φ) = tp2 φ ψ := by
  ext p; simp [mul_comm]

/-! ### Acceptance projections -/

/-- A two-copy test: an orthogonal projection on `H ⊗ H` that commutes with the swap
operator. (We do not require support in the symmetric subspace.) -/
structure IsAcceptanceProjection (P : H2 ι →ₗ[ℂ] H2 ι) : Prop where
  symmetric : P.IsSymmetric
  idem : P ∘ₗ P = P
  swap_comm : ∀ f, P (swap2 f) = swap2 (P f)

/-- The acceptance probability `p(ψ) = ⟨ψ ⊗ ψ, P (ψ ⊗ ψ)⟩` (real-valued). -/
def accProb (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) : ℝ :=
  (⟪tp2 ψ ψ, P (tp2 ψ ψ)⟫_ℂ).re

/-- The contracted vector `K_ψ |ψ⟩ = (I ⊗ ⟨ψ|) P |ψ⟩^{⊗2}`. -/
def Kvec (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) : H ι :=
  WithLp.toLp 2 fun i => ∑ j, conj (ψ j) * P (tp2 ψ ψ) (i, j)

@[simp] lemma Kvec_apply (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) (i : ι) :
    Kvec P ψ i = ∑ j, conj (ψ j) * P (tp2 ψ ψ) (i, j) := rfl

/-- The second moment `q(ψ) = ‖K_ψ ψ‖²` (real-valued). -/
def qProb (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) : ℝ :=
  (⟪Kvec P ψ, Kvec P ψ⟫_ℂ).re

/-! ### The operators `P_{ab}` on three copies

We index the three copies by the three coordinates of `ι × ι × ι` (so copy 1 is `p.1`,
copy 2 is `p.2.1`, copy 3 is `p.2.2`). `P_{ab}` applies `P` to the slice in coordinates
`a, b` with the remaining coordinate fixed. -/

/-- `P₁₂ = P ⊗ I`. -/
def p12 (P : H2 ι →ₗ[ℂ] H2 ι) : H3 ι →ₗ[ℂ] H3 ι where
  toFun f := WithLp.toLp 2 fun p =>
    P (WithLp.toLp 2 fun q => f (q.1, q.2, p.2.2)) (p.1, p.2.1)
  map_add' f g := by
    ext p
    simp only [PiLp.add_apply]
    have h : (WithLp.toLp 2 fun q : ι × ι => f (q.1, q.2, p.2.2) + g (q.1, q.2, p.2.2))
        = (WithLp.toLp 2 fun q : ι × ι => f (q.1, q.2, p.2.2))
          + (WithLp.toLp 2 fun q : ι × ι => g (q.1, q.2, p.2.2)) := rfl
    rw [h, map_add, PiLp.add_apply]
  map_smul' c f := by
    ext p
    simp only [PiLp.smul_apply]
    have h : (WithLp.toLp 2 fun q : ι × ι => c • f (q.1, q.2, p.2.2))
        = c • (WithLp.toLp 2 fun q : ι × ι => f (q.1, q.2, p.2.2)) := rfl
    rw [h, map_smul, PiLp.smul_apply]
    rfl

/-- `P₂₃ = I ⊗ P`. -/
def p23 (P : H2 ι →ₗ[ℂ] H2 ι) : H3 ι →ₗ[ℂ] H3 ι where
  toFun f := WithLp.toLp 2 fun p =>
    P (WithLp.toLp 2 fun q => f (p.1, q.1, q.2)) (p.2.1, p.2.2)
  map_add' f g := by
    ext p
    simp only [PiLp.add_apply]
    have h : (WithLp.toLp 2 fun q : ι × ι => f (p.1, q.1, q.2) + g (p.1, q.1, q.2))
        = (WithLp.toLp 2 fun q : ι × ι => f (p.1, q.1, q.2))
          + (WithLp.toLp 2 fun q : ι × ι => g (p.1, q.1, q.2)) := rfl
    rw [h, map_add, PiLp.add_apply]
  map_smul' c f := by
    ext p
    simp only [PiLp.smul_apply]
    have h : (WithLp.toLp 2 fun q : ι × ι => c • f (p.1, q.1, q.2))
        = c • (WithLp.toLp 2 fun q : ι × ι => f (p.1, q.1, q.2)) := rfl
    rw [h, map_smul, PiLp.smul_apply]
    rfl

/-- `P₁₃`: `P` acting on the first and third copies. -/
def p13 (P : H2 ι →ₗ[ℂ] H2 ι) : H3 ι →ₗ[ℂ] H3 ι where
  toFun f := WithLp.toLp 2 fun p =>
    P (WithLp.toLp 2 fun q => f (q.1, p.2.1, q.2)) (p.1, p.2.2)
  map_add' f g := by
    ext p
    simp only [PiLp.add_apply]
    have h : (WithLp.toLp 2 fun q : ι × ι => f (q.1, p.2.1, q.2) + g (q.1, p.2.1, q.2))
        = (WithLp.toLp 2 fun q : ι × ι => f (q.1, p.2.1, q.2))
          + (WithLp.toLp 2 fun q : ι × ι => g (q.1, p.2.1, q.2)) := rfl
    rw [h, map_add, PiLp.add_apply]
  map_smul' c f := by
    ext p
    simp only [PiLp.smul_apply]
    have h : (WithLp.toLp 2 fun q : ι × ι => c • f (q.1, p.2.1, q.2))
        = c • (WithLp.toLp 2 fun q : ι × ι => f (q.1, p.2.1, q.2)) := rfl
    rw [h, map_smul, PiLp.smul_apply]
    rfl

/-- The symmetrized three-copy operator `S = (P₁₂ + P₁₃ + P₂₃)/3` (eq:def-S). -/
def Sop (P : H2 ι →ₗ[ℂ] H2 ι) : H3 ι →ₗ[ℂ] H3 ι :=
  (3 : ℂ)⁻¹ • (p12 P + p13 P + p23 P)

/-! ### Action of `P_{ab}` on elementary tensors -/

omit fintypeι in
lemma p12_tp3 [Fintype ι] (P : H2 ι →ₗ[ℂ] H2 ι) (ψ φ χ : H ι) :
    p12 P (tp3 ψ φ χ)
      = WithLp.toLp 2 fun p => P (tp2 ψ φ) (p.1, p.2.1) * χ p.2.2 := by
  ext p
  simp only [p12, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  have h : (WithLp.toLp 2 fun q : ι × ι => tp3 ψ φ χ (q.1, q.2, p.2.2))
      = χ p.2.2 • tp2 ψ φ := by
    ext q
    simp only [tp3_apply, PiLp.smul_apply, tp2_apply, smul_eq_mul]
    ring
  rw [h, map_smul, PiLp.smul_apply, smul_eq_mul]
  ring

omit fintypeι in
lemma p23_tp3 [Fintype ι] (P : H2 ι →ₗ[ℂ] H2 ι) (ψ φ χ : H ι) :
    p23 P (tp3 ψ φ χ)
      = WithLp.toLp 2 fun p => ψ p.1 * P (tp2 φ χ) (p.2.1, p.2.2) := by
  ext p
  simp only [p23, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  have h : (WithLp.toLp 2 fun q : ι × ι => tp3 ψ φ χ (p.1, q.1, q.2))
      = ψ p.1 • tp2 φ χ := by
    ext q
    simp only [tp3_apply, PiLp.smul_apply, tp2_apply, smul_eq_mul]
    ring
  rw [h, map_smul, PiLp.smul_apply, smul_eq_mul]

omit fintypeι in
lemma p13_tp3 [Fintype ι] (P : H2 ι →ₗ[ℂ] H2 ι) (ψ φ χ : H ι) :
    p13 P (tp3 ψ φ χ)
      = WithLp.toLp 2 fun p => φ p.2.1 * P (tp2 ψ χ) (p.1, p.2.2) := by
  ext p
  simp only [p13, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  have h : (WithLp.toLp 2 fun q : ι × ι => tp3 ψ φ χ (q.1, p.2.1, q.2))
      = φ p.2.1 • tp2 ψ χ := by
    ext q
    simp only [tp3_apply, PiLp.smul_apply, tp2_apply, smul_eq_mul]
    ring
  rw [h, map_smul, PiLp.smul_apply, smul_eq_mul]

end

end GaussianTesting
