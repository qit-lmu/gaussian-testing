module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.PlaneUnitaries
public import GaussianTesting.Fermions.MajoranaCommutant

@[expose] public section

/-!
# The two parity orbits of coordinate Gaussian states

The elementary two-bit flips are products of two Majoranas and hence are plane
rotations. They connect any two occupation vectors of the same parity. Together
with parity preservation, this identifies exactly the even and odd orbits,
independently of the Gaussian certainty theorem.
-/

namespace GaussianTesting
open Finset
noncomputable section
variable {m : ℕ}

/-- The eigenvalue of the parity operator on an occupation vector. -/
def occupationParity (x : Qm m) : ℂ := (-1) ^ (univ.filter fun k => x k).card

theorem occupationParity_ne_zero (x : Qm m) : occupationParity x ≠ 0 := by
  simp [occupationParity]

theorem parityOp_single (x : Qm m) :
    parityOp (EuclideanSpace.single x (1 : ℂ)) =
      occupationParity x • EuclideanSpace.single x (1 : ℂ) := by
  ext y
  by_cases h : y = x
  · subst y; rfl
  · simp [EuclideanSpace.single, h, parityOp_apply]

theorem occupationParity_flipBit (k : Fin m) (x : Qm m) :
    occupationParity (flipBit k x) = -occupationParity x := by
  have h := congrArg (fun T : HF m →ₗ[ℂ] HF m => T (EuclideanSpace.single x (1 : ℂ)))
    (parityOp_anticomm_maj (k, false))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    majorana_false_single, map_smul, parityOp_single] at h
  have hc := congrArg (fun f : HF m => f (flipBit k x)) h
  simp at hc
  have hn : jwSign x k ≠ 0 := by
    have hnorm := norm_jwSign x k
    intro hz
    simp [hz] at hnorm
  apply (mul_left_cancel₀ hn)
  linear_combination hc

/-- Two distinct bit flips can be implemented by a plane rotation and a phase. -/
theorem exists_planeUnitary_doubleFlip (a b : Fin m) (hab : a ≠ b) (x : Qm m) :
    ∃ U : HF m ≃ₗᵢ[ℂ] HF m, U ∈ planeUnitaryGroup m ∧
      U (EuclideanSpace.single x 1) = EuclideanSpace.single (flipBit a (flipBit b x)) 1 := by
  let u := givensEquiv 0 1 (by norm_num) (a, false) (b, false) (by simpa using hab)
  let c := jwSign x b * jwSign (flipBit b x) a
  have hc : ‖c‖ = 1 := by simp [c, norm_jwSign]
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hu : u (EuclideanSpace.single x 1) =
      c • EuclideanSpace.single (flipBit a (flipBit b x)) 1 := by
    simp [u, givensU, majorana_false_single, map_smul, smul_smul, c]
  refine ⟨fermionPhaseEquiv c⁻¹ (by simp [norm_inv, hc]) * u,
    (planeUnitaryGroup m).mul_mem (fermionPhaseEquiv_mem_planeUnitaryGroup _ _)
      (givensEquiv_mem_planeUnitaryGroup _ _ _ _ _ _), ?_⟩
  change c⁻¹ • u (EuclideanSpace.single x 1) = _
  rw [hu, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- Occupation vectors with the same parity are in a single orbit. -/
theorem exists_planeUnitary_basis_of_parity_eq (x y : Qm m)
    (hpar : occupationParity x = occupationParity y) :
    ∃ U : HF m ≃ₗᵢ[ℂ] HF m, U ∈ planeUnitaryGroup m ∧
      U (EuclideanSpace.single x 1) = EuclideanSpace.single y 1 := by
  classical
  suffices h : ∀ s : Finset (Fin m), ∀ x y : Qm m,
      (∀ k, k ∉ s → x k = y k) → occupationParity x = occupationParity y →
      ∃ U : HF m ≃ₗᵢ[ℂ] HF m, U ∈ planeUnitaryGroup m ∧
        U (EuclideanSpace.single x 1) = EuclideanSpace.single y 1 by
    exact h univ x y (by simp) hpar
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hxy hp
    have he : x = y := funext (fun k => hxy k (by simp))
    subst y
    exact ⟨1, (planeUnitaryGroup m).one_mem, rfl⟩
  | @insert a s ha ih =>
    intro x y hxy hp
    by_cases he : x a = y a
    · apply ih x y ?_ hp
      intro k hk
      by_cases hka : k = a
      · subst k; exact he
      · exact hxy k (by simp [hk, hka])
    · let z := flipBit a x
      have hza : z a = y a := by
        cases hxa : x a <;> cases hya : y a <;> simp_all [z, flipBit]
      have hzy : z ≠ y := by
        intro hz
        have hneg := occupationParity_flipBit a x
        change occupationParity z = -occupationParity x at hneg
        rw [hz, ← hp] at hneg
        have hz0 : occupationParity x = 0 := by linear_combination hneg / 2
        exact occupationParity_ne_zero x hz0
      obtain ⟨b, hb⟩ : ∃ b, z b ≠ y b := by
        by_contra h
        exact hzy (funext (by simpa using h))
      have hba : b ≠ a := by rintro rfl; exact hb hza
      have hbs : b ∈ s := by
        by_contra hbs
        have hx := hxy b (by simp [hba, hbs])
        exact hb (by simpa [z, flipBit, hba] using hx)
      let w := flipBit b z
      have hwa : w a = y a := by simpa [w, flipBit, Ne.symm hba] using hza
      have hwy (k : Fin m) (hk : k ∉ s) : w k = y k := by
        by_cases hka : k = a
        · subst k; exact hwa
        · have hkb : k ≠ b := by rintro rfl; exact hk hbs
          simpa [w, z, flipBit, hka, hkb] using hxy k (by simp [hk, hka])
      have hwp : occupationParity w = occupationParity y := by
        simp only [w, z, occupationParity_flipBit, neg_neg]
        exact hp
      obtain ⟨U, hU, hUw⟩ := ih w y hwy hwp
      obtain ⟨V, hV, hVx⟩ := exists_planeUnitary_doubleFlip b a hba x
      refine ⟨U * V, (planeUnitaryGroup m).mul_mem hU hV, ?_⟩
      change U (V _) = _
      rw [hVx]
      exact hUw

/-- The Gaussian orbit of any occupation vector consists precisely of the
Gaussian states in its parity eigenspace. -/
theorem exists_planeUnitary_basis_iff (x : Qm m) (ψ : HF m) :
    (∃ U : HF m ≃ₗᵢ[ℂ] HF m, U ∈ planeUnitaryGroup m ∧
      U (EuclideanSpace.single x 1) = ψ) ↔
    IsGaussian ψ ∧ parityOp ψ = occupationParity x • ψ := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    constructor
    · apply (planeUnitary_isGaussian_iff hU _).mpr
      simpa using IsGaussian.basis x 1 (by simp)
    · rw [planeUnitary_parity hU, parityOp_single, map_smul]
  · rintro ⟨hψ, hp⟩
    obtain ⟨U, hU, y, rfl⟩ := (isGaussian_iff_exists_planeUnitary_basis ψ).mp hψ
    have hxy : occupationParity x = occupationParity y := by
      rw [planeUnitary_parity hU, parityOp_single, map_smul] at hp
      have hn : U (EuclideanSpace.single y (1 : ℂ)) ≠ 0 := by
        intro hz
        have hnorm := U.norm_map (EuclideanSpace.single y (1 : ℂ))
        simp [hz] at hnorm
      exact (smul_left_injective ℂ hn hp).symm
    obtain ⟨V, hV, hVx⟩ := exists_planeUnitary_basis_of_parity_eq x y hxy
    refine ⟨U * V, (planeUnitaryGroup m).mul_mem hU hV, ?_⟩
    change U (V _) = _
    rw [hVx]

end
end GaussianTesting
