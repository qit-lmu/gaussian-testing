module

/-
The two-copy operator `Λ = Σ_j c_j ⊗ c_j` characterizing fermionic Gaussian states,
and its kernel projection `P` (Section 5.1 of the paper).

The test accepts a unit vector `ψ` with certainty exactly when `Λ (ψ⊗ψ) = 0`.
`Covariance.lean` proves that this condition is equivalent to `IsGaussian ψ` in
Jordan–Wigner coordinates. The quantitative theorem uses the kernel condition.
-/
public import GaussianTesting.Fermions.JordanWigner
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {m : ℕ}

/-! ### Operators acting on one tensor factor of `H ⊗ H` -/

/-- `A ⊗ I`: apply `A` to the first factor. -/
def opL {ι : Type*} (A : H ι →ₗ[ℂ] H ι) : H2 ι →ₗ[ℂ] H2 ι where
  toFun f := WithLp.toLp 2 fun p => A (WithLp.toLp 2 fun i => f (i, p.2)) p.1
  map_add' f g := by
    ext p
    simp only [PiLp.add_apply]
    have h : (WithLp.toLp 2 fun i => f (i, p.2) + g (i, p.2))
        = (WithLp.toLp 2 fun i => f (i, p.2)) + (WithLp.toLp 2 fun i => g (i, p.2)) := rfl
    rw [h, map_add, PiLp.add_apply]
  map_smul' c f := by
    ext p
    simp only [PiLp.smul_apply]
    have h : (WithLp.toLp 2 fun i => c • f (i, p.2))
        = c • (WithLp.toLp 2 fun i => f (i, p.2)) := rfl
    rw [h, map_smul, PiLp.smul_apply]
    rfl

/-- `I ⊗ B`: apply `B` to the second factor. -/
def opR {ι : Type*} (B : H ι →ₗ[ℂ] H ι) : H2 ι →ₗ[ℂ] H2 ι where
  toFun f := WithLp.toLp 2 fun p => B (WithLp.toLp 2 fun j => f (p.1, j)) p.2
  map_add' f g := by
    ext p
    simp only [PiLp.add_apply]
    have h : (WithLp.toLp 2 fun j => f (p.1, j) + g (p.1, j))
        = (WithLp.toLp 2 fun j => f (p.1, j)) + (WithLp.toLp 2 fun j => g (p.1, j)) := rfl
    rw [h, map_add, PiLp.add_apply]
  map_smul' c f := by
    ext p
    simp only [PiLp.smul_apply]
    have h : (WithLp.toLp 2 fun j => c • f (p.1, j))
        = c • (WithLp.toLp 2 fun j => f (p.1, j)) := rfl
    rw [h, map_smul, PiLp.smul_apply]
    rfl

/-- Action on elementary tensors: `(A ⊗ I)(ψ ⊗ φ) = (Aψ) ⊗ φ`. -/
lemma opL_tp2 {ι : Type*} (A : H ι →ₗ[ℂ] H ι) (ψ φ : H ι) :
    opL A (tp2 ψ φ) = tp2 (A ψ) φ := by
  ext p
  change A (WithLp.toLp 2 fun i => ψ i * φ p.2) p.1 = A ψ p.1 * φ p.2
  have h : (WithLp.toLp 2 fun i => ψ i * φ p.2) = φ p.2 • ψ := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h, map_smul, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Action on elementary tensors: `(I ⊗ B)(ψ ⊗ φ) = ψ ⊗ (Bφ)`. -/
lemma opR_tp2 {ι : Type*} (B : H ι →ₗ[ℂ] H ι) (ψ φ : H ι) :
    opR B (tp2 ψ φ) = tp2 ψ (B φ) := by
  ext p
  change B (WithLp.toLp 2 fun j => ψ p.1 * φ j) p.2 = ψ p.1 * B φ p.2
  have h : (WithLp.toLp 2 fun j => ψ p.1 * φ j) = ψ p.1 • φ := rfl
  rw [h, map_smul, PiLp.smul_apply, smul_eq_mul]

/-- `opL` and `opR` commute. (Finiteness is necessary: for infinite `ι` there are
counterexamples built from functionals vanishing on finitely supported vectors.) -/
lemma opL_opR_comm {ι : Type*} [Fintype ι]
    (A B : H ι →ₗ[ℂ] H ι) : opL A ∘ₗ opR B = opR B ∘ₗ opL A := by
  classical
  apply LinearMap.ext
  intro f
  have hf : f = ∑ i : ι, ∑ j : ι, f (i, j) •
      tp2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    ext p
    simp [WithLp.ofLp_sum, Finset.sum_apply, tp2_apply, EuclideanSpace.single,
      PiLp.single_apply, smul_eq_mul]
  rw [hf]
  simp only [map_sum, map_smul, LinearMap.comp_apply, opL_tp2, opR_tp2]

private lemma opL_isSymmetric {ι : Type*} [Fintype ι]
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

private lemma opR_isSymmetric {ι : Type*} [Fintype ι]
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

private lemma swap2_opL {ι : Type*} [Fintype ι]
    (A : H ι →ₗ[ℂ] H ι) (f : H2 ι) : swap2 (opL A f) = opR A (swap2 f) := by
  ext p
  rfl

private lemma swap2_opR {ι : Type*} [Fintype ι]
    (A : H ι →ₗ[ℂ] H ι) (f : H2 ι) : swap2 (opR A f) = opL A (swap2 f) := by
  ext p
  rfl

/-! ### The Gaussianity operator `Λ` -/

/-- `Λ = Σ_{a} c_a ⊗ c_a`, the sum over all 2m Majorana operators. -/
def lambdaF (m : ℕ) : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) :=
  ∑ a : Fin m × Bool, opL (maj a) ∘ₗ opR (maj a)

/-- `Λ` is Hermitian. -/
lemma lambdaF_isSymmetric : (lambdaF m).IsSymmetric := by
  apply LinearMap.isSymmetric_sum
  intro a _ f g
  change inner ℂ (opL (maj a) (opR (maj a) f)) g =
    inner ℂ f (opL (maj a) (opR (maj a) g))
  rw [opL_isSymmetric (maj_isSymmetric a), opR_isSymmetric (maj_isSymmetric a)]
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    opL_opR_comm]

/-- `Λ` commutes with the swap operator. -/
lemma lambdaF_swap_comm (f : H2 (Qm m)) :
    lambdaF m (swap2 f) = swap2 (lambdaF m f) := by
  simp only [lambdaF, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [swap2_opL, swap2_opR]
  exact LinearMap.congr_fun (opL_opR_comm (maj a) (maj a)) (swap2 f)

/-! ### The accepting projection `P` -/

/-- The accepting projection of the fermionic test: the orthogonal projection onto
`ker Λ`. -/
def PF (m : ℕ) : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) :=
  ((LinearMap.ker (lambdaF m)).starProjection : H2 (Qm m) →L[ℂ] H2 (Qm m))

/-- `P` is an acceptance projection in the sense of the abstract theory. -/
theorem PF_isAcceptanceProjection (m : ℕ) : IsAcceptanceProjection (PF m) := by
  let K := LinearMap.ker (lambdaF m)
  refine ⟨K.starProjection_isSymmetric, ?_, ?_⟩
  · apply LinearMap.ext
    intro f
    exact K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem f)
  · intro f
    have inv (g : H2 (Qm m)) : swap2 (swap2 g) = g := by ext p; rfl
    have preserve {g : H2 (Qm m)} (hg : g ∈ K) : swap2 g ∈ K := by
      change lambdaF m (swap2 g) = 0
      rw [lambdaF_swap_comm, LinearMap.mem_ker.mp hg, map_zero]
    change K.starProjection (swap2 f) = swap2 (K.starProjection f)
    apply K.eq_starProjection_of_mem_of_inner_eq_zero
      (preserve (K.starProjection_apply_mem f))
    intro w hw
    have hz := K.starProjection_inner_eq_zero f (swap2 w) (preserve hw)
    rw [← map_sub]
    simpa only [swap2.inner_map_map, inv] using
      (show inner ℂ (swap2 (f - K.starProjection f)) (swap2 (swap2 w)) = 0 by
        rw [swap2.inner_map_map]; exact hz)

/-- The "good" set is exactly the kernel condition: for a unit vector,
`p(ψ) = 1 ↔ Λ ψ⊗ψ = 0`. -/
theorem accProb_PF_eq_one_iff {ψ : HF m} (hψ : ‖ψ‖ = 1) :
    accProb (PF m) ψ = 1 ↔ lambdaF m (tp2 ψ ψ) = 0 := by
  let x := tp2 ψ ψ
  let K := LinearMap.ker (lambdaF m)
  have hn : inner ℂ ψ ψ = 1 := by simp [inner_self_eq_norm_sq_to_K, hψ]
  have hx2 : ‖x‖ ^ 2 = 1 := by
    have ht : inner ℂ x x = 1 := by
      change inner ℂ (tp2 ψ ψ) (tp2 ψ ψ) = 1
      rw [inner_tp2_tp2, hn, mul_one]
    have hr := congrArg (RCLike.re : ℂ → ℝ) ht
    rw [inner_self_eq_norm_sq] at hr
    exact hr
  have hx : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
  have hp : accProb (PF m) ψ = ‖K.starProjection x‖ ^ 2 := by
    change (inner ℂ x (K.starProjection x)).re = _
    rw [← K.inner_starProjection_left_eq_right]
    exact K.re_inner_starProjection_eq_normSq x
  rw [hp]
  change ‖K.starProjection x‖ ^ 2 = 1 ↔ x ∈ K
  rw [K.mem_iff_norm_starProjection, hx]
  constructor <;> intro h
  · nlinarith [norm_nonneg (K.starProjection x)]
  · rw [h]; norm_num

/-- The vacuum (any occupation basis state, here `x ≡ false`) satisfies the kernel
condition — so the good set is nonempty. -/
theorem lambdaF_tp2_basisState :
    lambdaF m (tp2 (EuclideanSpace.single (fun _ => false) (1 : ℂ))
      (EuclideanSpace.single (fun _ => false) (1 : ℂ))) = 0 := by
  classical
  let e : HF m := EuclideanSpace.single (fun _ => false) 1
  have hm (k : Fin m) : maj (k, true) e = Complex.I • maj (k, false) e := by
    ext x
    by_cases h : flipBit k x = (fun _ => false)
    · have hk : x k = true := by
        have hh := congrFun h k
        simpa [flipBit] using hh
      simp [maj_apply, majFactor, hk, PiLp.smul_apply, smul_eq_mul]
      ring
    · simp [maj_apply, e, EuclideanSpace.single, h, PiLp.smul_apply]
  have ht (v : HF m) : tp2 (Complex.I • v) (Complex.I • v) = -tp2 v v := by
    ext p
    simp only [tp2_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
    calc
      _ = (Complex.I * Complex.I) * (v p.1 * v p.2) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  change lambdaF m (tp2 e e) = 0
  simp only [lambdaF, LinearMap.sum_apply, LinearMap.comp_apply, opR_tp2, opL_tp2,
    Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro k _
  simp [hm, ht]

end

end GaussianTesting
