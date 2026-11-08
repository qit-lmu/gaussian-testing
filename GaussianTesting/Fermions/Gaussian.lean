module

/-
Fermionic Gaussian states in Jordan–Wigner coordinates and the implication from
Gaussianity to the kernel condition in Lemma 5.1 (`lem:exact fermions`).

**Definition.** `IsGaussian ψ` means that `ψ` is obtained from an occupation
basis vector of either parity, up to phase, by a finite product of unitaries

    U(α,β; a,b) = α·1 + β·c_a c_b          (α² + β² = 1, a ≠ b),

which realize the planar Majorana rotations by angle 2θ for (α,β) = (cos θ, sin θ).
`GaussianOrbits.lean` identifies `IsGaussian` with the manuscript's union
of even and odd SO(2m) Gaussian-unitary orbits. The unused alternative
description by unique quadratic-Hamiltonian ground states is not developed.

**Results.** `givensU` is unitary with inverse `U(α,−β)`; it conjugates the Majoranas
by the planar rotation (`givensU_conj_*`); `Λ` is invariant under `U ⊗ U`
(`lambdaF_givens_comm`); `Λ (e_x ⊗ e_x) = 0` for every basis state; hence
`IsGaussian ψ → Λ ψ⊗ψ = 0` (`IsGaussian.lambdaF_eq_zero`) — direction (i) ⇒ (ii) of
`lem:exact fermions` — and `IsGaussian ψ → ‖ψ‖ = 1`.
-/
public import GaussianTesting.Fermions.Lambda

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {m : ℕ}

/-- The Givens unitary `α + β c_a c_b` in the Majorana plane `(a, b)`. -/
def givensU (α β : ℝ) (a b : Fin m × Bool) : HF m →ₗ[ℂ] HF m :=
  (α : ℂ) • LinearMap.id + (β : ℂ) • (maj a ∘ₗ maj b)

/-- States obtained from any occupation basis vector, up to phase, by a finite
product of unitaries implementing Majorana plane rotations. -/
inductive IsGaussian : HF m → Prop
  | basis (x : Qm m) (c : ℂ) (hc : ‖c‖ = 1) :
      IsGaussian (c • EuclideanSpace.single x (1 : ℂ))
  | givens {ψ : HF m} (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1)
      (a b : Fin m × Bool) (hab : a ≠ b) :
      IsGaussian ψ → IsGaussian (givensU α β a b ψ)

/-! ### Pointwise CAR facts -/

private lemma maj_maj_self (a : Fin m × Bool) (f : HF m) : maj a (maj a f) = f :=
  congrArg (fun T : HF m →ₗ[ℂ] HF m => T f) (maj_sq a)

private lemma maj_maj_swap {a b : Fin m × Bool} (hab : a ≠ b) (f : HF m) :
    maj b (maj a f) = -(maj a (maj b f)) := by
  have h := congrArg (fun T : HF m →ₗ[ℂ] HF m => T f) (maj_anticomm hab)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

private lemma givensU_apply (α β : ℝ) (a b : Fin m × Bool) (f : HF m) :
    givensU α β a b f = (α : ℂ) • f + (β : ℂ) • maj a (maj b f) := rfl

/-- `U(α,−β)` inverts `U(α,β)`. -/
lemma givensU_comp_inv {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 = 1)
    {a b : Fin m × Bool} (hab : a ≠ b) :
    givensU α β a b ∘ₗ givensU α (-β) a b = LinearMap.id := by
  have hc : ((α : ℂ)) ^ 2 + (β : ℂ) ^ 2 = 1 := by exact_mod_cast hαβ
  refine LinearMap.ext fun f => ?_
  have h4 : maj a (maj b (maj a (maj b f))) = -f := by
    rw [maj_maj_swap hab (maj b f), map_neg, maj_maj_self b, maj_maj_self a]
  simp only [LinearMap.comp_apply, LinearMap.id_apply, givensU_apply, map_add,
    map_smul, Complex.ofReal_neg, h4]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
  linear_combination (f i) * hc

/-- `U(α,−β)` also left-inverts `U(α,β)`. -/
lemma givensU_inv_comp {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 = 1)
    {a b : Fin m × Bool} (hab : a ≠ b) :
    givensU α (-β) a b ∘ₗ givensU α β a b = LinearMap.id := by
  have h := givensU_comp_inv (α := α) (β := -β) (by simpa using hαβ) hab
  simpa [neg_neg] using h

/-- The adjoint relation: `⟪U f, g⟫ = ⟪f, U(α,−β) g⟫` (for a genuine plane, `a ≠ b`;
otherwise `maj a ∘ maj a = id` and `U` is the self-adjoint `(α+β)·id`). -/
lemma givensU_adjoint (α β : ℝ) {a b : Fin m × Bool} (hab : a ≠ b) (f g : HF m) :
    ⟪givensU α β a b f, g⟫_ℂ = ⟪f, givensU α (-β) a b g⟫_ℂ := by
  simp only [givensU_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, Complex.ofReal_neg]
  have h1 : ⟪maj a (maj b f), g⟫_ℂ = -⟪f, maj a (maj b g)⟫_ℂ := by
    rw [maj_isSymmetric a, maj_isSymmetric b, maj_maj_swap hab g, inner_neg_right]
  rw [h1]
  ring

/-- Givens rotations are isometries. -/
lemma norm_givensU {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 = 1)
    {a b : Fin m × Bool} (hab : a ≠ b) (ψ : HF m) :
    ‖givensU α β a b ψ‖ = ‖ψ‖ := by
  have h : ⟪givensU α β a b ψ, givensU α β a b ψ⟫_ℂ = ⟪ψ, ψ⟫_ℂ := by
    rw [givensU_adjoint α β hab]
    congr 1
    exact congrArg (fun T : HF m →ₗ[ℂ] HF m => T ψ) (givensU_inv_comp hαβ hab)
  have hr := congrArg Complex.re h
  change RCLike.re ⟪_, _⟫_ℂ = RCLike.re ⟪_, _⟫_ℂ at hr
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at hr
  nlinarith [norm_nonneg (givensU α β a b ψ), norm_nonneg ψ]

/-- Conjugation of the first plane Majorana: with `p := α² − β²`, `q := 2αβ`,
`U c_a U⁻¹ = p c_a − q c_b`. -/
lemma givensU_conj_fst {α β : ℝ} (_hαβ : α ^ 2 + β ^ 2 = 1)
    {a b : Fin m × Bool} (hab : a ≠ b) :
    givensU α β a b ∘ₗ maj a ∘ₗ givensU α (-β) a b
      = ((α ^ 2 - β ^ 2 : ℝ) : ℂ) • maj a - ((2 * α * β : ℝ) : ℂ) • maj b := by
  refine LinearMap.ext fun f => ?_
  have h1 : maj a (maj b (maj a f)) = -(maj b f) := by
    rw [maj_maj_swap hab f, map_neg, maj_maj_self a]
  have h2 : maj a (maj a (maj b f)) = maj b f := maj_maj_self a _
  have h3 : maj a (maj b (maj a (maj a (maj b f)))) = maj a f := by
    rw [maj_maj_self a, maj_maj_self b]
  have hbb : maj a (maj b (maj b f)) = maj a f := by rw [maj_maj_self b]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    givensU_apply, map_add, map_smul, Complex.ofReal_neg, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, h1, h2, hbb]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, PiLp.sub_apply,
    smul_eq_mul]
  ring

/-- `U c_b U⁻¹ = q c_a + p c_b`. -/
lemma givensU_conj_snd {α β : ℝ} (_hαβ : α ^ 2 + β ^ 2 = 1)
    {a b : Fin m × Bool} (hab : a ≠ b) :
    givensU α β a b ∘ₗ maj b ∘ₗ givensU α (-β) a b
      = ((2 * α * β : ℝ) : ℂ) • maj a + ((α ^ 2 - β ^ 2 : ℝ) : ℂ) • maj b := by
  refine LinearMap.ext fun f => ?_
  have h1 : maj b (maj a (maj b f)) = -(maj a (maj b (maj b f))) :=
    maj_maj_swap hab (maj b f)
  have h2 : maj a (maj b (maj b f)) = maj a f := by rw [maj_maj_self b]
  have h3 : maj a (maj b (maj b (maj a (maj b f)))) = maj a (maj a (maj b f)) := by
    rw [maj_maj_self b]
  have h4 : maj a (maj a (maj b f)) = maj b f := maj_maj_self a _
  have hbb : maj a (maj b (maj b f)) = maj a f := by rw [maj_maj_self b]
  have h5 : maj a (maj b (maj a f)) = -(maj b f) := by
    rw [maj_maj_swap hab f, map_neg, maj_maj_self a]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    givensU_apply, map_add, map_smul, map_neg, Complex.ofReal_neg,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, h1, h2, h5]
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
    smul_eq_mul]
  ring

/-- `U c_e U⁻¹ = c_e` for `e ∉ {a, b}`. -/
lemma givensU_conj_other {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 = 1)
    {a b e : Fin m × Bool} (hab : a ≠ b) (hea : e ≠ a) (heb : e ≠ b) :
    givensU α β a b ∘ₗ maj e ∘ₗ givensU α (-β) a b = maj e := by
  refine LinearMap.ext fun f => ?_
  have hcomm (g : HF m) : maj e (maj a (maj b g)) = maj a (maj b (maj e g)) := by
    rw [maj_maj_swap hea.symm (maj b g), maj_maj_swap heb.symm g, map_neg, neg_neg]
  have hswap : maj e (givensU α (-β) a b f) = givensU α (-β) a b (maj e f) := by
    simp only [givensU_apply, map_add, map_smul, Complex.ofReal_neg, hcomm]
  simp only [LinearMap.comp_apply]
  rw [hswap]
  exact congrArg (fun T : HF m →ₗ[ℂ] HF m => T (maj e f)) (givensU_comp_inv hαβ hab)

/-! ### Operator-argument linearity of the slot embeddings (pointwise) -/

private lemma opL_comp_apply (A B : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opL A (opL B g) = opL (A ∘ₗ B) g := rfl

private lemma opR_comp_apply (A B : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opR A (opR B g) = opR (A ∘ₗ B) g := rfl

private lemma opL_add_apply (A B : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opL (A + B) g = opL A g + opL B g := by
  ext p; rfl

private lemma opR_add_apply (A B : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opR (A + B) g = opR A g + opR B g := by
  ext p; rfl

private lemma opL_sub_apply (A B : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opL (A - B) g = opL A g - opL B g := by
  ext p; rfl

private lemma opR_sub_apply (A B : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opR (A - B) g = opR A g - opR B g := by
  ext p; rfl

private lemma opL_smul_apply (c : ℂ) (A : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opL (c • A) g = c • opL A g := by
  ext p; rfl

private lemma opR_smul_apply (c : ℂ) (A : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opR (c • A) g = c • opR A g := by
  ext p; rfl

private lemma opL_opR_comm_apply (A B : HF m →ₗ[ℂ] HF m) (g : H2 (Qm m)) :
    opL A (opR B g) = opR B (opL A g) :=
  congrArg (fun T : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) => T g) (opL_opR_comm A B)

/-- `Λ` commutes with `U ⊗ U` for a Givens unitary `U` (eq:Lambda-Gaussian-invariance
for the generators). -/
lemma lambdaF_givens_comm {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 = 1)
    {a b : Fin m × Bool} (hab : a ≠ b) :
    lambdaF m ∘ₗ (opL (givensU α β a b) ∘ₗ opR (givensU α β a b))
      = (opL (givensU α β a b) ∘ₗ opR (givensU α β a b)) ∘ₗ lambdaF m := by
  classical
  set U := givensU α β a b with hU
  set V := givensU α (-β) a b with hV
  have hVU : V ∘ₗ U = LinearMap.id := givensU_inv_comp hαβ hab
  -- conjugated Majoranas
  set D : (Fin m × Bool) → (HF m →ₗ[ℂ] HF m) := fun c => U ∘ₗ maj c ∘ₗ V with hD
  have hUc (c : Fin m × Bool) : U ∘ₗ maj c = D c ∘ₗ U := by
    simp only [hD, LinearMap.comp_assoc, hVU, LinearMap.comp_id]
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.comp_apply, lambdaF, LinearMap.sum_apply, map_sum]
  -- rewrite both sides into D-form against the common vector g := opL U (opR U f)
  have hL (c : Fin m × Bool) :
      opL U (opR U (opL (maj c) (opR (maj c) f)))
        = opL (D c) (opR (D c) (opL U (opR U f))) := by
    rw [← opL_opR_comm_apply (maj c) U, opL_comp_apply, opR_comp_apply,
      hUc c, ← opL_comp_apply, ← opR_comp_apply, opL_opR_comm_apply U (D c)]
  rw [Finset.sum_congr rfl fun c _ => hL c]
  -- now prove Σ_c T_c g = Σ_c (D c)-version at g
  set g := opL U (opR U f) with hg
  have hpair : opL (D a) (opR (D a) g) + opL (D b) (opR (D b) g)
      = opL (maj a) (opR (maj a) g) + opL (maj b) (opR (maj b) g) := by
    have hfst : D a = ((α ^ 2 - β ^ 2 : ℝ) : ℂ) • maj a
        - ((2 * α * β : ℝ) : ℂ) • maj b := by
      simp only [hD, hU, hV]
      exact givensU_conj_fst hαβ hab
    have hsnd : D b = ((2 * α * β : ℝ) : ℂ) • maj a
        + ((α ^ 2 - β ^ 2 : ℝ) : ℂ) • maj b := by
      simp only [hD, hU, hV]
      exact givensU_conj_snd hαβ hab
    have hpq : ((α ^ 2 - β ^ 2 : ℝ) : ℂ) ^ 2 + ((2 * α * β : ℝ) : ℂ) ^ 2 = 1 := by
      have : (α ^ 2 - β ^ 2) ^ 2 + (2 * α * β) ^ 2 = 1 := by nlinarith [hαβ]
      exact_mod_cast this
    rw [hfst, hsnd]
    simp only [opL_sub_apply, opL_add_apply, opL_smul_apply, opR_sub_apply,
      opR_add_apply, opR_smul_apply, map_sub, map_add, map_smul]
    ext p
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination (opL (maj a) (opR (maj a) g) p
      + opL (maj b) (opR (maj b) g) p) * hpq
  have hrest (c : Fin m × Bool) (hca : c ≠ a) (hcb : c ≠ b) : D c = maj c := by
    simp only [hD, hU, hV]
    exact givensU_conj_other hαβ hab hca hcb
  -- split both sums over {a, b} and the rest
  have hsplit (T : (Fin m × Bool) → H2 (Qm m)) :
      ∑ c, T c = T a + T b + ∑ c ∈ (univ.erase a).erase b, T c := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
    abel
  rw [hsplit (fun c => opL (D c) (opR (D c) g)),
    hsplit (fun c => opL (maj c) (opR (maj c) g)), hpair]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨hcb, hca, -⟩ : c ≠ b ∧ c ≠ a ∧ True := by
    simp only [Finset.mem_erase] at hc
    exact ⟨hc.1, hc.2.1, trivial⟩
  rw [hrest c hca hcb]

/-- Every occupation basis state is annihilated: `Λ (e_x ⊗ e_x) = 0` (the X- and
Y-type Majorana contributions cancel mode by mode, as in `lambdaF_tp2_basisState`). -/
lemma lambdaF_tp2_single (x : Qm m) :
    lambdaF m (tp2 (EuclideanSpace.single x (1 : ℂ)) (EuclideanSpace.single x (1 : ℂ)))
      = 0 := by
  classical
  set e : HF m := EuclideanSpace.single x 1 with he
  set s : Fin m → ℂ := fun k => if x k then -Complex.I else Complex.I with hs
  have hm (k : Fin m) : maj (k, true) e = s k • maj (k, false) e := by
    ext y
    by_cases h : flipBit k y = x
    · have hk : y k = !x k := by
        have hh := congrFun h k
        simp only [flipBit, Function.update_self] at hh
        cases hy : y k <;> cases hx : x k <;> simp_all
      cases hx : x k <;>
        simp [maj_apply, majFactor, hk, hx, h, he, hs, PiLp.smul_apply,
          smul_eq_mul, EuclideanSpace.single] <;> ring
    · simp [maj_apply, he, EuclideanSpace.single, h,
        PiLp.smul_apply]
  have hs2 (k : Fin m) : s k * s k = -1 := by
    cases hx : x k <;> simp [hs, hx, Complex.I_mul_I]
  have ht (k : Fin m) (v : HF m) : tp2 (s k • v) (s k • v) = -tp2 v v := by
    ext p
    simp only [tp2_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
    calc s k * v p.1 * (s k * v p.2) = (s k * s k) * (v p.1 * v p.2) := by ring
      _ = -(v p.1 * v p.2) := by rw [hs2]; ring
  change lambdaF m (tp2 e e) = 0
  simp only [lambdaF, LinearMap.sum_apply, LinearMap.comp_apply, opR_tp2, opL_tp2,
    Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro k _
  simp [hm, ht]

/-- Direction (i) ⇒ (ii) of `lem:exact fermions`: Gaussian states are in the kernel. -/
theorem IsGaussian.lambdaF_eq_zero {ψ : HF m} (hψ : IsGaussian ψ) :
    lambdaF m (tp2 ψ ψ) = 0 := by
  induction hψ with
  | basis x c hc =>
      have hb : tp2 (c • EuclideanSpace.single x (1 : ℂ))
          (c • EuclideanSpace.single x (1 : ℂ))
          = (c * c) • tp2 (EuclideanSpace.single x (1 : ℂ))
              (EuclideanSpace.single x (1 : ℂ)) := by
        ext p
        simp only [tp2_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [hb, map_smul, lambdaF_tp2_single, smul_zero]
  | @givens φ α β hαβ a b hab hφ ih =>
      have ht : tp2 (givensU α β a b φ) (givensU α β a b φ)
          = opL (givensU α β a b) (opR (givensU α β a b) (tp2 φ φ)) := by
        rw [opR_tp2, opL_tp2]
      rw [ht]
      have h := congrArg
        (fun T : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) => T (tp2 φ φ))
        (lambdaF_givens_comm hαβ hab)
      simp only [LinearMap.comp_apply] at h
      rw [h, ih, map_zero, map_zero]

/-- Gaussian states are unit vectors. -/
theorem IsGaussian.norm_eq_one {ψ : HF m} (hψ : IsGaussian ψ) : ‖ψ‖ = 1 := by
  induction hψ with
  | basis x c hc =>
      rw [norm_smul, hc, one_mul]
      simp [EuclideanSpace.single, PiLp.norm_single]
  | @givens φ α β hαβ a b hab hφ ih =>
      rw [norm_givensU hαβ hab, ih]

/-- If applying a Majorana plane rotation sends `ψ` into `IsGaussian`, then
`ψ` also belongs to `IsGaussian`. -/
theorem IsGaussian.of_givens {ψ : HF m} {α β : ℝ} (hαβ : α ^ 2 + β ^ 2 = 1)
    {a b : Fin m × Bool} (hab : a ≠ b)
    (h : IsGaussian (givensU α β a b ψ)) : IsGaussian ψ := by
  have h2 := IsGaussian.givens α (-β) (by simpa using hαβ) a b hab h
  have h3 : givensU α (-β) a b (givensU α β a b ψ) = ψ :=
    congrArg (fun T : HF m →ₗ[ℂ] HF m => T ψ) (givensU_inv_comp hαβ hab)
  rwa [h3] at h2

end

end GaussianTesting
