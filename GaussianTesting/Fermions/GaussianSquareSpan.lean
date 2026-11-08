module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.BellEigenvalues
public import GaussianTesting.Fermions.GaussianCertainty

@[expose] public section

/-!
# The span of the fermionic Gaussian squares

The span includes both Gaussian parity orbits. It is invariant under the
Majorana pair involutions and simultaneous Gaussian rotations. The Bell
basis diagonalizes those involutions, so the orthogonal projection onto the
span preserves each joint Bell eigenline. A vacuum-square overlap supplies
one such line, and permutations of the Majorana coordinates supply every
zero-eigenvalue line.
-/

namespace GaussianTesting

open scoped InnerProductSpace
open Finset

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {m : ℕ}

/-- The linear span of the squares of the manuscript's two Gaussian orbits. -/
def fermionicGaussianSquareSpan (m : ℕ) : Submodule ℂ (H2 (Qm m)) :=
  Submodule.span ℂ ((fun ψ => tp2 ψ ψ) '' fermionicGaussianStates m)

theorem fermionicGaussianSquareSpan_le_kernel (m : ℕ) :
    fermionicGaussianSquareSpan m ≤ LinearMap.ker (lambdaF m) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨ψ, hψ, rfl⟩
  exact fermionicGaussian_lambdaF_eq_zero hψ

private abbrev pairMajorana (a : Fin m × Bool) : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) :=
  opL (maj a) ∘ₗ opR (maj a)

private abbrev bellEigen (z : Qm m × Qm m) (a : Fin m × Bool) : ℤ :=
  fermionicBellMajoranaEigenvalue z a

private theorem pairMajorana_basis (a : Fin m × Bool) (z : Qm m × Qm m) :
    pairMajorana a (fermionicBellBasis m z) =
      (bellEigen z a : ℂ) • fermionicBellBasis m z := by
  simpa only [pairMajorana, bellEigen, LinearMap.comp_apply, fermionicBellBasis_apply]
    using majoranaPair_fermionicBellVector z a

private theorem pairMajorana_lambda (a : Fin m × Bool) (f : H2 (Qm m)) :
    lambdaF m (pairMajorana a f) = pairMajorana a (lambdaF m f) := by
  rw [← (fermionicBellBasis m).sum_repr f]
  simp only [map_sum, map_smul, pairMajorana_basis, lambdaF_fermionicBellBasis,
    smul_smul, mul_comm, mul_left_comm]

private theorem norm_majorana (a : Fin m × Bool) (ψ : HF m) : ‖maj a ψ‖ = ‖ψ‖ := by
  have hs : maj a (maj a ψ) = ψ := LinearMap.congr_fun (maj_sq a) ψ
  have h := congrArg Complex.re ((maj_isSymmetric a) ψ (maj a ψ))
  rw [hs, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  simp only [← RCLike.ofReal_pow] at h
  change (↑(‖maj a ψ‖ ^ 2) : ℂ).re = (↑(‖ψ‖ ^ 2) : ℂ).re at h
  simp only [Complex.ofReal_re] at h
  nlinarith [norm_nonneg (maj a ψ), norm_nonneg ψ]

private theorem gaussian_majorana (a : Fin m × Bool) {ψ : HF m}
    (hψ : ψ ∈ fermionicGaussianStates m) : maj a ψ ∈ fermionicGaussianStates m := by
  apply fermionicGaussian_of_lambdaF_eq_zero
  · rw [norm_majorana]
    exact ((mem_fermionicGaussianStates_iff ψ).mp hψ).norm_eq_one
  · have h := pairMajorana_lambda a (tp2 ψ ψ)
    simpa only [LinearMap.comp_apply, opR_tp2, opL_tp2,
      fermionicGaussian_lambdaF_eq_zero hψ, map_zero] using h

private theorem squareSpan_majorana (a : Fin m × Bool) {f : H2 (Qm m)}
    (hf : f ∈ fermionicGaussianSquareSpan m) :
    pairMajorana a f ∈ fermionicGaussianSquareSpan m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, rfl⟩ := hf
    simp only [pairMajorana, LinearMap.comp_apply, opR_tp2, opL_tp2]
    exact Submodule.subset_span ⟨maj a ψ, gaussian_majorana a hψ, rfl⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg ihf ihg =>
    rw [map_add]; exact Submodule.add_mem _ ihf ihg
  | smul c f hf ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

private theorem squareSpan_gaussian {U : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : U ∈ gaussianUnitaryGroup m) {f : H2 (Qm m)}
    (hf : f ∈ fermionicGaussianSquareSpan m) :
    fermionPairAction U f ∈ fermionicGaussianSquareSpan m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, rfl⟩ := hf
    have hG : U ψ ∈ fermionicGaussianStates m := by
      rw [mem_fermionicGaussianStates_iff] at hψ ⊢
      exact (planeUnitary_isGaussian_iff
        (by simpa only [gaussianUnitaryGroup_eq_planeUnitaryGroup] using hU) ψ).mpr hψ
    rw [fermionPairAction_tp2]
    exact Submodule.subset_span ⟨U ψ, hG, rfl⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg ihf ihg => rw [map_add]; exact Submodule.add_mem _ ihf ihg
  | smul c f hf ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

private theorem bellSign_sq (b : Bool) : fermionicBellSign b ^ 2 = 1 := by
  cases b <;> norm_num [fermionicBellSign]

private theorem bellEigen_sq (z : Qm m × Qm m) (a : Fin m × Bool) :
    bellEigen z a ^ 2 = 1 := by
  simp only [fermionicBellMajoranaEigenvalue, mul_pow, ← Finset.prod_pow, bellSign_sq,
    Finset.prod_const_one, one_mul]
  cases a.2 <;> simp [bellSign_sq]

private theorem bellEigen_ne_zero (z : Qm m × Qm m) (a : Fin m × Bool) :
    bellEigen z a ≠ 0 := by
  intro h
  have := bellEigen_sq z a
  simp [h] at this

private theorem bellSign_injective : Function.Injective fermionicBellSign := by decide

private theorem bellEigen_true (z : Qm m × Qm m) (k : Fin m) :
    bellEigen z (k, true) = -fermionicBellSign (z.2 k) * bellEigen z (k, false) := by
  simp only [fermionicBellMajoranaEigenvalue, Bool.false_eq_true, ↓reduceIte]
  ring

private theorem bellEigen_injective : Function.Injective (bellEigen (m := m)) := by
  intro z w h
  have hb : z.2 = w.2 := by
    funext k
    apply bellSign_injective
    have he := congrFun h (k, true)
    rw [bellEigen_true, bellEigen_true, congrFun h (k, false)] at he
    exact neg_injective (mul_right_cancel₀ (bellEigen_ne_zero w (k, false)) he)
  apply Prod.ext _ hb
  funext k
  apply bellSign_injective
  have he := congrFun h (k, false)
  simp only [fermionicBellMajoranaEigenvalue, Bool.false_eq_true, ↓reduceIte,
    mul_one, hb] at he
  apply mul_left_cancel₀ (b := fermionicBellSign (z.1 k)) (c := fermionicBellSign (w.1 k))
    (a := ∏ l ∈ univ.filter (fun l => l < k), fermionicBellSign (w.2 l)) _ he
  apply Finset.prod_ne_zero_iff.mpr
  intro l _
  cases w.2 l <;> norm_num [fermionicBellSign]

private theorem pairMajorana_repr (a : Fin m × Bool) (f : H2 (Qm m))
    (z : Qm m × Qm m) :
    (fermionicBellBasis m).repr (pairMajorana a f) z =
      (bellEigen z a : ℂ) * (fermionicBellBasis m).repr f z := by
  conv_lhs => rw [← (fermionicBellBasis m).sum_repr f]
  simp only [map_sum, map_smul, pairMajorana_basis, OrthonormalBasis.repr_self,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  simp [EuclideanSpace.single, PiLp.single_apply, mul_comm]

private theorem pairMajorana_symmetric (a : Fin m × Bool) :
    (pairMajorana a).IsSymmetric := by
  intro f g
  rw [← (fermionicBellBasis m).sum_repr f]
  simp only [map_sum, map_smul, sum_inner, inner_smul_left]
  apply Finset.sum_congr rfl
  intro z _
  have h := pairMajorana_repr a g z
  simp only [OrthonormalBasis.repr_apply_apply] at h
  rw [pairMajorana_basis, inner_smul_left, h]
  simp only [map_intCast]

private theorem joint_eigenvector_eq (z : Qm m × Qm m) (f : H2 (Qm m))
    (hf : ∀ a, pairMajorana a f = (bellEigen z a : ℂ) • f) :
    f = (fermionicBellBasis m).repr f z • fermionicBellBasis m z := by
  apply (fermionicBellBasis m).repr.injective
  rw [map_smul, OrthonormalBasis.repr_self]
  ext w
  by_cases hwz : w = z
  · subst w
    simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  · have hc : (fermionicBellBasis m).repr f w = 0 := by
      by_contra hne
      have he : bellEigen w = bellEigen z := by
        funext a
        have h := congrArg (fun g => (fermionicBellBasis m).repr g w) (hf a)
        rw [pairMajorana_repr] at h
        simp only [map_smul, PiLp.smul_apply, smul_eq_mul] at h
        have he' : (bellEigen w a : ℂ) = (bellEigen z a : ℂ) :=
          mul_right_cancel₀ hne h
        exact_mod_cast he'
      exact hwz (bellEigen_injective he)
    simp [EuclideanSpace.single, hc, hwz]

private theorem squareSpan_projection_majorana (a : Fin m × Bool) (f : H2 (Qm m)) :
    (fermionicGaussianSquareSpan m).starProjection (pairMajorana a f) =
      pairMajorana a ((fermionicGaussianSquareSpan m).starProjection f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (squareSpan_majorana a ((fermionicGaussianSquareSpan m).starProjection_apply_mem f))
  intro w hw
  rw [← map_sub, pairMajorana_symmetric]
  exact (fermionicGaussianSquareSpan m).starProjection_inner_eq_zero f _
    (squareSpan_majorana a hw)

private theorem squareSpan_basis_of_overlap (z : Qm m × Qm m)
    {f : H2 (Qm m)} (hf : f ∈ fermionicGaussianSquareSpan m)
    (hoverlap : inner ℂ (fermionicBellBasis m z) f ≠ 0) :
    fermionicBellBasis m z ∈ fermionicGaussianSquareSpan m := by
  let W := fermionicGaussianSquareSpan m
  let v := fermionicBellBasis m z
  have heig (a : Fin m × Bool) :
      pairMajorana a (W.starProjection v) = (bellEigen z a : ℂ) • W.starProjection v := by
    rw [← squareSpan_projection_majorana, pairMajorana_basis, map_smul]
  obtain hc := joint_eigenvector_eq z (W.starProjection v) heig
  let c := (fermionicBellBasis m).repr (W.starProjection v) z
  change W.starProjection v = c • v at hc
  have hcn : c ≠ 0 := by
    intro hz
    have h := W.starProjection_isSymmetric v f
    change inner ℂ (W.starProjection v) f = inner ℂ v (W.starProjection f) at h
    rw [hc, hz, zero_smul, inner_zero_left, W.starProjection_eq_self_iff.mpr hf] at h
    exact hoverlap h.symm
  have hmem : c • v ∈ W := hc ▸ W.starProjection_apply_mem v
  exact (Submodule.smul_mem_iff W hcn).mp hmem

private abbrev zeroBell (m : ℕ) : Qm m × Qm m :=
  (fun _ => false, fun _ => false)

private theorem zeroBell_eigen (a : Fin m × Bool) :
    bellEigen (zeroBell m) a = if a.2 then -1 else 1 := by
  rcases a with ⟨k, b⟩
  cases b <;> simp [fermionicBellMajoranaEigenvalue, zeroBell, fermionicBellSign]

private theorem zeroBell_mem_squareSpan (m : ℕ) :
    fermionicBellBasis m (zeroBell m) ∈ fermionicGaussianSquareSpan m := by
  let e : HF m := EuclideanSpace.single (fun _ => false) 1
  have he : e ∈ fermionicGaussianStates m := by
    rw [mem_fermionicGaussianStates_iff]
    simpa only [one_smul] using IsGaussian.basis (fun _ => false) 1 (by simp)
  apply squareSpan_basis_of_overlap (zeroBell m)
    (Submodule.subset_span ⟨e, he, rfl⟩)
  have ht : tp2 e e = EuclideanSpace.single (zeroBell m) 1 := by
    ext p
    by_cases h1 : p.1 = fun _ => false <;>
      by_cases h2 : p.2 = fun _ => false <;>
      simp [tp2_apply, e, EuclideanSpace.single, PiLp.single_apply, zeroBell,
        Prod.ext_iff, h1, h2]
  change inner ℂ (fermionicBellBasis m (zeroBell m)) (tp2 e e) ≠ 0
  rw [ht, EuclideanSpace.inner_single_right]
  have hb : bellScale ≠ 0 :=
    inv_ne_zero (by exact_mod_cast
      (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)))
  simp [fermionicBellBasis_apply, fermionicBellVector_apply, zeroBell,
    bellLocalAmplitude, hb]

private theorem exists_gaussian_majoranaSwap (a b : Fin m × Bool) (hab : a ≠ b) :
    ∃ U : HF m ≃ₗᵢ[ℂ] HF m, U ∈ gaussianUnitaryGroup m ∧
      ∀ e, ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ ψ,
        U (maj e ψ) = (s : ℂ) • maj (Equiv.swap a b e) (U ψ) := by
  obtain ⟨U, hU, hrot⟩ :=
    exists_planeUnitary_implements_planeRotation a b hab 0 1 (by norm_num)
  refine ⟨U, planeUnitaryGroup_le_gaussianUnitaryGroup hU, fun e => ?_⟩
  let s : ℝ := if e = a then -1 else 1
  refine ⟨s, by dsimp [s]; split_ifs <;> norm_num, fun ψ => ?_⟩
  have h := hrot.majorana e (U ψ)
  simp only [U.symm_apply_apply] at h
  have hcol (k : Fin m × Bool) :
      planeRotationMatrix a b 0 1 k e = if k = Equiv.swap a b e then s else 0 := by
    by_cases hea : e = a
    · subst e
      rw [Equiv.swap_apply_left]
      by_cases hka : k = a
      · subst k; simp [planeRotationMatrix, s, hab]
      · simp [planeRotationMatrix, s, hka]
    · by_cases heb : e = b
      · subst e
        rw [Equiv.swap_apply_right]
        by_cases hka : k = a
        · subst k; simp [planeRotationMatrix, s, hab.symm]
        · by_cases hkb : k = b
          · subst k; simp [planeRotationMatrix, s, hab.symm]
          · simp [planeRotationMatrix, s, hka, hkb]
      · rw [Equiv.swap_apply_of_ne_of_ne hea heb]
        by_cases hka : k = a
        · subst k; simp [planeRotationMatrix, s, hea, heb, Ne.symm hea]
        · by_cases hkb : k = b
          · subst k; simp [planeRotationMatrix, s, hea, heb, Ne.symm heb]
          · simp [planeRotationMatrix, s, hka, hkb, hea]
  change U (maj e ψ) = ∑ k, (planeRotationMatrix a b 0 1 k e : ℂ) • maj k (U ψ) at h
  rw [h]
  simp only [hcol, apply_ite, Complex.ofReal_zero, ite_smul, zero_smul]
  simp

private theorem exists_gaussian_majoranaPermutation (σ : Equiv.Perm (Fin m × Bool)) :
    ∃ U : HF m ≃ₗᵢ[ℂ] HF m, U ∈ gaussianUnitaryGroup m ∧
      ∀ a, ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ ψ,
        U (maj a ψ) = (s : ℂ) • maj (σ a) (U ψ) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    exact ⟨1, (gaussianUnitaryGroup m).one_mem, fun a =>
      ⟨1, by norm_num, fun ψ => by simp⟩⟩
  | swap_mul σ a b hab ih =>
    obtain ⟨U, hU, hσ⟩ := ih
    obtain ⟨V, hV, hswap⟩ := exists_gaussian_majoranaSwap a b hab
    refine ⟨V * U, (gaussianUnitaryGroup m).mul_mem hV hU, fun e => ?_⟩
    obtain ⟨s, hs, he⟩ := hσ e
    obtain ⟨t, ht, he'⟩ := hswap (σ e)
    refine ⟨s * t, by rw [mul_pow, hs, ht, one_mul], fun ψ => ?_⟩
    change V (U (maj e ψ)) = ((s * t : ℝ) : ℂ) •
      maj (Equiv.swap a b (σ e)) (V (U ψ))
    rw [he, map_smul, he', smul_smul, Complex.ofReal_mul]

private theorem pairAction_majoranaPermutation
    (σ : Equiv.Perm (Fin m × Bool)) (U : HF m ≃ₗᵢ[ℂ] HF m)
    (hU : ∀ a, ∃ s : ℝ, s ^ 2 = 1 ∧ ∀ ψ,
      U (maj a ψ) = (s : ℂ) • maj (σ a) (U ψ))
    (a : Fin m × Bool) (f : H2 (Qm m)) :
    fermionPairAction U (pairMajorana a f) =
      pairMajorana (σ a) (fermionPairAction U f) := by
  obtain ⟨s, hs, he⟩ := hU a
  have hpair (ψ φ : HF m) :
      fermionPairAction U (pairMajorana a (tp2 ψ φ)) =
        pairMajorana (σ a) (fermionPairAction U (tp2 ψ φ)) := by
    simp only [pairMajorana, LinearMap.comp_apply, opR_tp2, opL_tp2,
      fermionPairAction_tp2, he]
    ext p
    simp only [tp2_apply, PiLp.smul_apply, smul_eq_mul]
    have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
    linear_combination (maj (σ a) (U ψ) p.1 * maj (σ a) (U φ) p.2) * hs'
  have hf : f = ∑ i : Qm m, ∑ j : Qm m, f (i, j) •
      tp2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    ext p
    simp [WithLp.ofLp_sum, Finset.sum_apply, tp2_apply, EuclideanSpace.single,
      PiLp.single_apply, smul_eq_mul]
  rw [hf]
  simp only [map_sum, map_smul, hpair]

private theorem bellEigen_sum (z : Qm m × Qm m) :
    (∑ a, bellEigen z a) = fermionicBellEigenvalue m z := by
  simp only [fermionicBellEigenvalue, Fintype.sum_prod_type, Fintype.sum_bool,
    fermionicBellMajoranaEigenvalue, Bool.false_eq_true, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem bellEigen_pos_card (z : Qm m × Qm m)
    (hz : fermionicBellEigenvalue m z = 0) :
    Fintype.card {a : Fin m × Bool // bellEigen z a = 1} = m := by
  classical
  let p := fun a : Fin m × Bool => bellEigen z a = 1
  have hsum : (Fintype.card {a // p a} : ℤ) - Fintype.card {a // ¬p a} = 0 := by
    have h := (bellEigen_sum z).trans hz
    rw [← Fintype.sum_subtype_add_sum_subtype p (bellEigen z)] at h
    have hpos (a : {a // p a}) : bellEigen z a = 1 := a.2
    have hneg (a : {a // ¬p a}) : bellEigen z a = -1 :=
      (sq_eq_one_iff.mp (bellEigen_sq z a)).resolve_left a.2
    simpa only [hpos, hneg, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, mul_neg, sub_eq_add_neg] using h
  have hcard : Fintype.card {a // p a} + Fintype.card {a // ¬p a} = 2 * m := by
    have h := Fintype.card_congr (Equiv.sumCompl p)
    simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, mul_comm] using h
  change Fintype.card {a // p a} = m
  omega

private def modeBoolSum (m : ℕ) : (Fin m × Bool) ≃ (Fin m ⊕ Fin m) where
  toFun a := if a.2 then Sum.inr a.1 else Sum.inl a.1
  invFun a := a.elim (fun k => (k, false)) (fun k => (k, true))
  left_inv a := by rcases a with ⟨k, b⟩; cases b <;> rfl
  right_inv a := by cases a <;> rfl

private theorem exists_balanced_permutation (z : Qm m × Qm m)
    (hz : fermionicBellEigenvalue m z = 0) :
    ∃ σ : Equiv.Perm (Fin m × Bool), ∀ a,
      bellEigen z (σ a) = bellEigen (zeroBell m) a := by
  classical
  let p := fun a : Fin m × Bool => bellEigen z a = 1
  have hp : Fintype.card {a // p a} = m := bellEigen_pos_card z hz
  have hn : Fintype.card {a // ¬p a} = m := by
    rw [Fintype.card_subtype_compl, hp]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  let ep : Fin m ≃ {a // p a} := Fintype.equivOfCardEq (by simpa using hp.symm)
  let en : Fin m ≃ {a // ¬p a} := Fintype.equivOfCardEq (by simpa using hn.symm)
  let σ : Equiv.Perm (Fin m × Bool) :=
    ((modeBoolSum m).trans (Equiv.sumCongr ep en)).trans (Equiv.sumCompl p)
  refine ⟨σ, ?_⟩
  rintro ⟨k, b⟩
  rw [zeroBell_eigen]
  cases b
  · change bellEigen z (ep k).1 = 1
    exact (ep k).2
  · change bellEigen z (en k).1 = -1
    exact (sq_eq_one_iff.mp (bellEigen_sq z (en k))).resolve_left (en k).2

private theorem balancedBell_mem_squareSpan (z : Qm m × Qm m)
    (hz : fermionicBellEigenvalue m z = 0) :
    fermionicBellBasis m z ∈ fermionicGaussianSquareSpan m := by
  obtain ⟨σ, hσ⟩ := exists_balanced_permutation z hz
  obtain ⟨U, hU, hperm⟩ := exists_gaussian_majoranaPermutation σ
  let f := fermionPairAction U (fermionicBellBasis m (zeroBell m))
  have hmem : f ∈ fermionicGaussianSquareSpan m :=
    squareSpan_gaussian hU (zeroBell_mem_squareSpan m)
  have heig (a : Fin m × Bool) :
      pairMajorana a f = (bellEigen z a : ℂ) • f := by
    obtain ⟨b, rfl⟩ := σ.surjective a
    dsimp only [f]
    rw [← pairAction_majoranaPermutation σ U hperm, pairMajorana_basis,
      map_smul, hσ]
  have he := joint_eigenvector_eq z f heig
  have hf : f ≠ 0 := by
    intro hf
    have h := fermionPairAction_symm_apply U.symm (fermionicBellBasis m (zeroBell m))
    change fermionPairAction U.symm f = fermionicBellBasis m (zeroBell m) at h
    rw [hf, map_zero] at h
    exact (fermionicBellBasis m).toBasis.ne_zero (zeroBell m) h.symm
  have hc : (fermionicBellBasis m).repr f z ≠ 0 := by
    intro hc
    exact hf (he.trans (by rw [hc, zero_smul]))
  exact (Submodule.smul_mem_iff (fermionicGaussianSquareSpan m) hc).mp (he ▸ hmem)

/-- The assertion following Lemma 5.1: the kernel is spanned by squares of
Gaussian states from both parity sectors. The state class is independently
defined by the even and odd SO(2m) orbits. -/
theorem fermionicGaussianSquareSpan_eq_kernel (m : ℕ) :
    fermionicGaussianSquareSpan m = LinearMap.ker (lambdaF m) := by
  apply le_antisymm (fermionicGaussianSquareSpan_le_kernel m)
  intro f hf
  rw [← (fermionicBellBasis m).sum_repr f]
  apply Submodule.sum_mem
  intro z _
  by_cases hz : fermionicBellEigenvalue m z = 0
  · exact Submodule.smul_mem _ _ (balancedBell_mem_squareSpan z hz)
  · have h := lambdaF_isSymmetric (fermionicBellBasis m z) f
    rw [lambdaF_fermionicBellBasis, LinearMap.mem_ker.mp hf, inner_zero_right,
      inner_smul_left] at h
    simp only [map_intCast] at h
    have hc : (fermionicBellBasis m).repr f z = 0 := by
      rw [OrthonormalBasis.repr_apply_apply]
      exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hz)
    rw [hc, zero_smul]
    exact Submodule.zero_mem _

/-- Every vector in the Gaussian-square span is symmetric under the copy swap. -/
theorem swap2_eq_self_of_mem_fermionicGaussianSquareSpan {f : H2 (Qm m)}
    (hf : f ∈ fermionicGaussianSquareSpan m) : swap2 f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, rfl⟩ := hf
    exact swap2_tp2 ψ ψ
  | zero => exact map_zero _
  | add f g hf hg ihf ihg => rw [map_add, ihf, ihg]
  | smul c f hf ih => rw [map_smul, ih]

/-- The fermionic accepting projection is supported on the symmetric subspace,
as asserted after Lemma 5.1. This holds on the full two-copy Hilbert space. -/
theorem swap2_PF (m : ℕ) (f : H2 (Qm m)) : swap2 (PF m f) = PF m f := by
  apply swap2_eq_self_of_mem_fermionicGaussianSquareSpan
  rw [fermionicGaussianSquareSpan_eq_kernel]
  exact (LinearMap.ker (lambdaF m)).starProjection_apply_mem f

end
end GaussianTesting
