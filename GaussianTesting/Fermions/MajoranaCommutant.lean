module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.Gaussian

@[expose] public section

/-!
# Uniqueness of fermionic Gaussian implementers up to phase

The Jordan--Wigner Majoranas have scalar commutant. Commuting with a Majorana
pair forces preservation of every one-dimensional occupation eigenspace;
commuting with the bit-flipping Majoranas makes its scalar independent of the
occupation vector. This supplies precisely the uniqueness needed to compare
implementers of the same orthogonal Majorana action.

This background argument does not use the certainty characterization of
Lemma 5.1.
-/

namespace GaussianTesting

open Finset

noncomputable section

variable {m : ℕ}

private lemma jwSign_flip_self (x : Qm m) (k : Fin m) :
    jwSign (flipBit k x) k = jwSign x k := by
  unfold jwSign
  apply Finset.prod_congr rfl
  intro l hl
  have hne : l ≠ k := ne_of_lt (Finset.mem_filter.mp hl).2
  simp [flipBit, Function.update_of_ne hne]

private lemma jwSign_sq (x : Qm m) (k : Fin m) :
    jwSign x k * jwSign x k = 1 := by
  unfold jwSign
  rw [← Finset.prod_mul_distrib]
  have h (b : Bool) : (if b then (-1 : ℂ) else 1) * (if b then -1 else 1) = 1 := by
    cases b <;> norm_num
  simp only [h, Finset.prod_const_one]

private lemma majorana_pair_apply (k : Fin m) (f : HF m) (x : Qm m) :
    Complex.I * (maj (k, false) (maj (k, true) f)) x =
      (if x k then 1 else -1) * f x := by
  simp only [maj_apply, jwSign_flip_self, flipBit_flipBit]
  simp only [flipBit, Function.update_self, majFactor]
  cases hx : x k <;> simp
  · calc
      _ = -(jwSign x k * jwSign x k) * f x := by
        linear_combination (jwSign x k * jwSign x k * f x) * Complex.I_mul_I
      _ = _ := by rw [jwSign_sq]; simp
  · calc
      _ = (jwSign x k * jwSign x k) * f x := by
        linear_combination -(jwSign x k * jwSign x k * f x) * Complex.I_mul_I
      _ = _ := by rw [jwSign_sq]; simp

private lemma majorana_pair_single (k : Fin m) (x : Qm m) :
    Complex.I • maj (k, false) (maj (k, true) (EuclideanSpace.single x (1 : ℂ))) =
      (if x k then (1 : ℂ) else -1) • EuclideanSpace.single x (1 : ℂ) := by
  ext y
  simp only [PiLp.smul_apply, smul_eq_mul, majorana_pair_apply]
  by_cases h : y = x
  · subst y; rfl
  · simp [EuclideanSpace.single, h]

private lemma commuting_map_basis (A : HF m →ₗ[ℂ] HF m)
    (hA : ∀ a, A ∘ₗ maj a = maj a ∘ₗ A) (x : Qm m) :
    A (EuclideanSpace.single x (1 : ℂ)) =
      A (EuclideanSpace.single x (1 : ℂ)) x • EuclideanSpace.single x (1 : ℂ) := by
  have hc (a : Fin m × Bool) (f : HF m) : A (maj a f) = maj a (A f) :=
    congrArg (fun T : HF m →ₗ[ℂ] HF m => T f) (hA a)
  have he (k : Fin m) :
      Complex.I • maj (k, false) (maj (k, true) (A (EuclideanSpace.single x (1 : ℂ)))) =
        (if x k then (1 : ℂ) else -1) • A (EuclideanSpace.single x (1 : ℂ)) := by
    rw [← hc, ← hc, ← map_smul, majorana_pair_single, map_smul]
  ext y
  by_cases hy : y = x
  · subst y; simp
  · have hk : ∃ k, y k ≠ x k := by
      by_contra hh
      exact hy (funext (by simpa using hh))
    obtain ⟨k, hk⟩ := hk
    have hv := congrArg (fun f : HF m => f y) (he k)
    simp only [PiLp.smul_apply, smul_eq_mul, majorana_pair_apply] at hv
    have hz : A (EuclideanSpace.single x (1 : ℂ)) y = 0 := by
      cases hyk : y k <;> cases hxk : x k <;> simp [hyk, hxk] at hk hv
      all_goals first | linear_combination hv / 2 | linear_combination -hv / 2
    simp [EuclideanSpace.single, hy, hz]

/-- An X-type Majorana flips the indicated occupation, with the Jordan--Wigner sign. -/
lemma majorana_false_single (k : Fin m) (x : Qm m) :
    maj (k, false) (EuclideanSpace.single x (1 : ℂ)) =
      jwSign x k • EuclideanSpace.single (flipBit k x) (1 : ℂ) := by
  ext y
  by_cases hy : y = flipBit k x
  · subst y
    simp [majFactor, jwSign_flip_self]
  · have hf : flipBit k y ≠ x := by
      intro h
      have := congrArg (flipBit k) h
      simp only [flipBit_flipBit] at this
      exact hy this
    simp [EuclideanSpace.single, hy, hf, majFactor]

/-- The Jordan--Wigner string sign has unit modulus. -/
lemma norm_jwSign (x : Qm m) (k : Fin m) : ‖jwSign x k‖ = 1 := by
  have h := congrArg norm (jwSign_sq x k)
  rw [norm_mul, norm_one] at h
  nlinarith [norm_nonneg (jwSign x k)]

private lemma occupation_induction (P : Qm m → Prop)
    (hzero : P (fun _ => false))
    (hflip : ∀ k x, P x → P (flipBit k x)) (x : Qm m) : P x := by
  classical
  have hs (s : Finset (Fin m)) : P (fun k => decide (k ∈ s)) := by
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a s ha ih =>
      have he : (fun k => decide (k ∈ insert a s)) =
          flipBit a (fun k => decide (k ∈ s)) := by
        funext k
        by_cases hk : k = a
        · subst k; simp [flipBit, ha]
        · simp [flipBit, hk]
      rw [he]
      exact hflip a _ ih
  simpa using hs (univ.filter (fun k => x k))

/-- A linear map commuting with all Jordan--Wigner Majoranas is a scalar.
This includes the zero-mode, one-dimensional Hilbert space. -/
theorem exists_scalar_of_commutes_maj (A : HF m →ₗ[ℂ] HF m)
    (hA : ∀ a, A ∘ₗ maj a = maj a ∘ₗ A) :
    ∃ c : ℂ, A = c • LinearMap.id := by
  classical
  let z : Qm m := fun _ => false
  let c : ℂ := A (EuclideanSpace.single z (1 : ℂ)) z
  have hb (x : Qm m) :
      A (EuclideanSpace.single x (1 : ℂ)) = c • EuclideanSpace.single x (1 : ℂ) := by
    apply occupation_induction (fun x =>
      A (EuclideanSpace.single x (1 : ℂ)) = c • EuclideanSpace.single x (1 : ℂ))
    · exact commuting_map_basis A hA z
    · intro k x hx
      have he := congrArg (fun T : HF m →ₗ[ℂ] HF m =>
        T (EuclideanSpace.single x (1 : ℂ))) (hA (k, false))
      simp only [LinearMap.comp_apply] at he
      rw [majorana_false_single, map_smul, hx, map_smul, majorana_false_single] at he
      have hs : jwSign x k ≠ 0 := by
        intro h
        have := jwSign_sq x k
        simp [h] at this
      apply (smul_right_injective _ hs)
      simpa only [smul_smul, mul_comm c] using he
  refine ⟨c, ?_⟩
  ext f x
  have hf : f = ∑ y : Qm m, f y • EuclideanSpace.single y (1 : ℂ) := by
    ext y
    simp [EuclideanSpace.single, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]
  rw [hf]
  simp only [map_sum, map_smul, hb, LinearMap.smul_apply, LinearMap.id_apply]

/-- Unitary maps commuting with every Majorana are global phases. -/
theorem exists_phase_of_commutes_maj (U : HF m ≃ₗᵢ[ℂ] HF m)
    (hU : ∀ a, U.toLinearEquiv.toLinearMap ∘ₗ maj a =
      maj a ∘ₗ U.toLinearEquiv.toLinearMap) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ ψ : HF m, U ψ = c • ψ := by
  obtain ⟨c, hc⟩ := exists_scalar_of_commutes_maj U.toLinearEquiv.toLinearMap hU
  have h (ψ : HF m) : U ψ = c • ψ :=
    congrArg (fun A : HF m →ₗ[ℂ] HF m => A ψ) hc
  refine ⟨c, ?_, h⟩
  have hn := U.norm_map (EuclideanSpace.single (fun _ => false) (1 : ℂ))
  rw [h, norm_smul] at hn
  simpa using hn

/-- Two unitaries with the same Majorana conjugation action differ only by
a global phase. No choice of lift enters the resulting orbit of rays. -/
theorem exists_phase_of_same_majorana_conjugation
    (U V : HF m ≃ₗᵢ[ℂ] HF m)
    (hUV : ∀ a ψ, U (maj a (U.symm ψ)) = V (maj a (V.symm ψ))) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ ψ : HF m, U ψ = c • V ψ := by
  let W : HF m ≃ₗᵢ[ℂ] HF m := U.trans V.symm
  have hW : ∀ a, W.toLinearEquiv.toLinearMap ∘ₗ maj a =
      maj a ∘ₗ W.toLinearEquiv.toLinearMap := by
    intro a
    apply LinearMap.ext
    intro ψ
    have h := congrArg V.symm (hUV a (U ψ))
    simpa [W] using h
  obtain ⟨c, hc, he⟩ := exists_phase_of_commutes_maj W hW
  refine ⟨c, hc, fun ψ => ?_⟩
  have h := congrArg V (he ψ)
  simpa [W] using h

end
end GaussianTesting
