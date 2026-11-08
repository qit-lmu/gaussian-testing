module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.Gaussian
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

/-!
# Gaussian implementers in Majorana coordinates

The index `Fin m × Bool` labels the `2m` Majoranas. An implementer of a real
special orthogonal matrix acts on their real linear combinations by that matrix.
This is the action in Eq. (5.1), before choosing its scalar phase.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- The manuscript's `SO(2m)`, indexed by mode and Majorana type. -/
abbrev FermionRotation (m : ℕ) := Matrix.specialOrthogonalGroup (Fin m × Bool) ℝ

/-- A real linear combination of the Jordan--Wigner Majoranas. -/
def majoranaCombination (v : (Fin m × Bool) → ℝ) : HF m →ₗ[ℂ] HF m :=
  ∑ a, (v a : ℂ) • maj a

@[simp] theorem majoranaCombination_single (a : Fin m × Bool) :
    majoranaCombination (Pi.single a (1 : ℝ)) = maj a := by
  classical
  simp [majoranaCombination, Pi.single_apply]

/-- A unitary implements a rotation when it has the prescribed Majorana action.
Using real combinations makes composition and inverses explicit. -/
def ImplementsMajoranaRotation (R : FermionRotation m) (U : HF m ≃ₗᵢ[ℂ] HF m) : Prop :=
  ∀ (v : (Fin m × Bool) → ℝ) (ψ : HF m),
    U (majoranaCombination v ψ) =
      majoranaCombination ((R : Matrix (Fin m × Bool) (Fin m × Bool) ℝ).mulVec v) (U ψ)

theorem ImplementsMajoranaRotation.one :
    ImplementsMajoranaRotation (1 : FermionRotation m) (1 : HF m ≃ₗᵢ[ℂ] HF m) := by
  intro v ψ
  simp

theorem ImplementsMajoranaRotation.mul {R S : FermionRotation m}
    {U V : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : ImplementsMajoranaRotation R U) (hV : ImplementsMajoranaRotation S V) :
    ImplementsMajoranaRotation (R * S) (U * V) := by
  intro v ψ
  change U (V (majoranaCombination v ψ)) =
    majoranaCombination (((R : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) * (S : Matrix (Fin m × Bool) (Fin m × Bool) ℝ)).mulVec v) (U (V ψ))
  rw [hV, hU, Matrix.mulVec_mulVec]

theorem ImplementsMajoranaRotation.inv {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U) :
    ImplementsMajoranaRotation R⁻¹ U⁻¹ := by
  intro v ψ
  apply U.injective
  have h := hU (((R⁻¹ : FermionRotation m) : Matrix (Fin m × Bool) (Fin m × Bool) ℝ).mulVec v) (U⁻¹ ψ)
  have hRR : (R : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) * ((R⁻¹ : FermionRotation m) : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) = 1 :=
    congrArg (fun A : FermionRotation m => (A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ)) (mul_inv_cancel R)
  simpa only [Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec,
    LinearIsometryEquiv.inv_def, LinearIsometryEquiv.apply_symm_apply] using h.symm

/-- The column form of the manuscript's conjugation law. -/
theorem ImplementsMajoranaRotation.majorana {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (a : Fin m × Bool) (ψ : HF m) :
    U (maj a (U.symm ψ)) = ∑ b, ((R : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) b a : ℂ) • maj b ψ := by
  have h := hU (Pi.single a 1) (U.symm ψ)
  simpa [majoranaCombination, Matrix.mulVec_single_one] using h

/-- It suffices to check the conjugation law on the individual Majoranas. -/
theorem implementsMajoranaRotation_of_columns (R : FermionRotation m)
    (U : HF m ≃ₗᵢ[ℂ] HF m)
    (h : ∀ (a : Fin m × Bool) (ψ : HF m),
      U (maj a ψ) = ∑ b, ((R : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) b a : ℂ) • maj b (U ψ)) :
    ImplementsMajoranaRotation R U := by
  intro v ψ
  simp only [majoranaCombination, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

/-- The unitaries satisfying the manuscript's Majorana action for some rotation. -/
def gaussianUnitaryGroup (m : ℕ) : Subgroup (HF m ≃ₗᵢ[ℂ] HF m) where
  carrier := {U | ∃ R : FermionRotation m, ImplementsMajoranaRotation R U}
  one_mem' := ⟨1, ImplementsMajoranaRotation.one⟩
  mul_mem' := by
    rintro U V ⟨R, hR⟩ ⟨S, hS⟩
    exact ⟨R * S, hR.mul hS⟩
  inv_mem' := by
    rintro U ⟨R, hR⟩
    exact ⟨R⁻¹, hR.inv⟩

end
end GaussianTesting
