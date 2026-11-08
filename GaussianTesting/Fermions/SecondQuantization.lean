module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.GaussianImplementers
public import GaussianTesting.Fermions.OccupationVacuum
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

/-!
# Second quantization of real mode rotations

A passive real rotation acts identically on the two Majorana types. Its
Gaussian implementer preserves the vacuum line. Fixing the vacuum removes
the phase ambiguity and gives the second-quantized action used in Section 5.
-/

namespace GaussianTesting

noncomputable section

open Matrix
open scoped Kronecker

variable {m : ℕ}

/-- Real special orthogonal rotations of the one-particle mode space. -/
abbrev FermionModeRotation (m : ℕ) := Matrix.specialOrthogonalGroup (Fin m) ℝ

/-- A real one-particle rotation acts identically on the X and Y Majoranas. -/
def passiveMajoranaRotation : FermionModeRotation m →* FermionRotation m where
  toFun R := ⟨R.val ⊗ₖ (1 : Matrix Bool Bool ℝ), by
    refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
    · apply (Matrix.mem_orthogonalGroup_iff' _ _).mpr
      have hR := (Matrix.mem_orthogonalGroup_iff' _ _).mp R.property.1
      rw [show (R.val ⊗ₖ (1 : Matrix Bool Bool ℝ))ᵀ =
          R.valᵀ ⊗ₖ (1 : Matrix Bool Bool ℝ) by ext; simp [Matrix.one_apply, eq_comm]]
      rw [← Matrix.mul_kronecker_mul, hR, one_mul, Matrix.one_kronecker_one]
    · have hd : R.val.det = 1 := R.property.2
      rw [Matrix.det_kronecker, hd, Matrix.det_one]
      simp⟩
  map_one' := by apply Subtype.ext; exact Matrix.one_kronecker_one
  map_mul' R S := by
    apply Subtype.ext
    change (R.val * S.val) ⊗ₖ (1 : Matrix Bool Bool ℝ) = _
    simpa using Matrix.mul_kronecker_mul R.val S.val
      (1 : Matrix Bool Bool ℝ) (1 : Matrix Bool Bool ℝ)

@[simp] theorem passiveMajoranaRotation_apply (R : FermionModeRotation m)
    (k l : Fin m) (a b : Bool) :
    (passiveMajoranaRotation R).val (k, a) (l, b) =
      if a = b then R.val k l else 0 := by
  simp [passiveMajoranaRotation, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Passive Majorana covariance keeps the X and Y types separate. -/
theorem ImplementsMajoranaRotation.passive_majorana
    {R : FermionModeRotation m} {U : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : ImplementsMajoranaRotation (passiveMajoranaRotation R) U)
    (k : Fin m) (a : Bool) (ψ : HF m) :
    U (maj (k, a) ψ) = ∑ l, (R.val l k : ℂ) • maj (l, a) (U ψ) := by
  have h := hU.majorana (k, a) (U ψ)
  cases a <;> simpa [Fintype.sum_prod_type, passiveMajoranaRotation_apply,
    Fintype.sum_bool] using h

/-- Passive rotations transform creation operators by the one-particle matrix. -/
theorem ImplementsMajoranaRotation.passive_creation
    {R : FermionModeRotation m} {U : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : ImplementsMajoranaRotation (passiveMajoranaRotation R) U)
    (k : Fin m) (ψ : HF m) :
    U (fermionCreation k ψ) = ∑ l, (R.val l k : ℂ) • fermionCreation l (U ψ) := by
  simp only [fermionCreation, LinearMap.smul_apply, LinearMap.sub_apply,
    map_smul, map_sub, hU.passive_majorana, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  module

/-- Passive rotations transform annihilation operators by the same real matrix. -/
theorem ImplementsMajoranaRotation.passive_annihilation
    {R : FermionModeRotation m} {U : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : ImplementsMajoranaRotation (passiveMajoranaRotation R) U)
    (k : Fin m) (ψ : HF m) :
    U (fermionAnnihilation k ψ) = ∑ l, (R.val l k : ℂ) • fermionAnnihilation l (U ψ) := by
  simp only [fermionAnnihilation, LinearMap.smul_apply, LinearMap.add_apply,
    map_smul, map_add, hU.passive_majorana, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  module

/-- A passive implementer preserves the vacuum line. -/
theorem ImplementsMajoranaRotation.passive_vacuum_line
    {R : FermionModeRotation m} {U : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : ImplementsMajoranaRotation (passiveMajoranaRotation R) U) :
    U (fermionVacuum m) =
      U (fermionVacuum m) (fun _ => false) • fermionVacuum m := by
  apply eq_smul_fermionVacuum_of_annihilation_eq_zero
  have hinv : ImplementsMajoranaRotation (passiveMajoranaRotation R⁻¹) U.symm := by
    simpa only [map_inv, LinearIsometryEquiv.inv_def] using hU.inv
  intro k
  apply U.symm.injective
  rw [map_zero, hinv.passive_annihilation]
  simp

def passiveVacuumPhase (R : FermionModeRotation m) : ℂ :=
  gaussianImplementer (passiveMajoranaRotation R) (fermionVacuum m) (fun _ => false)

private theorem norm_passiveVacuumPhase (R : FermionModeRotation m) :
    ‖passiveVacuumPhase R‖ = 1 := by
  have h := congrArg norm
    (gaussianImplementer_implements (passiveMajoranaRotation R)).passive_vacuum_line
  simpa [passiveVacuumPhase, norm_smul] using h.symm

def vacuumFixedImplementer (R : FermionModeRotation m) : HF m ≃ₗᵢ[ℂ] HF m :=
  fermionPhaseEquiv (passiveVacuumPhase R)⁻¹ (by simp [norm_passiveVacuumPhase]) *
    gaussianImplementer (passiveMajoranaRotation R)

private theorem vacuumFixedImplementer_implements (R : FermionModeRotation m) :
    ImplementsMajoranaRotation (passiveMajoranaRotation R) (vacuumFixedImplementer R) := by
  have hp := fermionPhaseEquiv_implements (m := m) (passiveVacuumPhase R)⁻¹
    (by simp [norm_passiveVacuumPhase])
  simpa [vacuumFixedImplementer] using
    hp.mul (gaussianImplementer_implements (passiveMajoranaRotation R))

private theorem vacuumFixedImplementer_vacuum (R : FermionModeRotation m) :
    vacuumFixedImplementer R (fermionVacuum m) = fermionVacuum m := by
  change (passiveVacuumPhase R)⁻¹ •
    gaussianImplementer (passiveMajoranaRotation R) (fermionVacuum m) = _
  rw [(gaussianImplementer_implements (passiveMajoranaRotation R)).passive_vacuum_line]
  change (passiveVacuumPhase R)⁻¹ • (passiveVacuumPhase R • fermionVacuum m) = _
  rw [smul_smul, inv_mul_cancel₀, one_smul]
  exact norm_ne_zero_iff.mp (by rw [norm_passiveVacuumPhase]; norm_num)

/-- Vacuum normalization removes the projective phase ambiguity. -/
theorem passiveImplementer_unique {R : FermionModeRotation m}
    {U V : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : ImplementsMajoranaRotation (passiveMajoranaRotation R) U)
    (hV : ImplementsMajoranaRotation (passiveMajoranaRotation R) V)
    (hUv : U (fermionVacuum m) = fermionVacuum m)
    (hVv : V (fermionVacuum m) = fermionVacuum m) : U = V := by
  obtain ⟨z, hz, hUV⟩ := hU.unique_phase hV
  have hv := hUV (fermionVacuum m)
  rw [hUv, hVv] at hv
  have hz1 : z = 1 := by
    have h := congrArg (fun ψ : HF m => ψ (fun _ => false)) hv
    simpa [fermionVacuum] using h.symm
  apply LinearIsometryEquiv.ext
  intro ψ
  simpa [hz1] using hUV ψ

/-- The vacuum-fixed second quantization of a real special orthogonal mode rotation. -/
def fermionSecondQuantization : FermionModeRotation m →* (HF m ≃ₗᵢ[ℂ] HF m) where
  toFun := vacuumFixedImplementer
  map_one' := by
    apply passiveImplementer_unique (R := 1) (vacuumFixedImplementer_implements 1)
      (by simpa using (ImplementsMajoranaRotation.one (m := m)))
      (vacuumFixedImplementer_vacuum 1)
    rfl
  map_mul' R S := by
    apply passiveImplementer_unique (R := R * S) (vacuumFixedImplementer_implements (R * S))
      (by simpa using ((vacuumFixedImplementer_implements R).mul
          (vacuumFixedImplementer_implements S))) (vacuumFixedImplementer_vacuum (R * S))
    change vacuumFixedImplementer R (vacuumFixedImplementer S (fermionVacuum m)) = _
    rw [vacuumFixedImplementer_vacuum, vacuumFixedImplementer_vacuum]

theorem fermionSecondQuantization_implements (R : FermionModeRotation m) :
    ImplementsMajoranaRotation (passiveMajoranaRotation R) (fermionSecondQuantization R) :=
  vacuumFixedImplementer_implements R

@[simp] theorem fermionSecondQuantization_vacuum (R : FermionModeRotation m) :
    fermionSecondQuantization R (fermionVacuum m) = fermionVacuum m :=
  vacuumFixedImplementer_vacuum R

theorem fermionSecondQuantization_creation (R : FermionModeRotation m)
    (k : Fin m) (ψ : HF m) :
    fermionSecondQuantization R (fermionCreation k ψ) =
      ∑ l, (R.val l k : ℂ) • fermionCreation l (fermionSecondQuantization R ψ) :=
  (fermionSecondQuantization_implements R).passive_creation k ψ

theorem fermionSecondQuantization_annihilation (R : FermionModeRotation m)
    (k : Fin m) (ψ : HF m) :
    fermionSecondQuantization R (fermionAnnihilation k ψ) =
      ∑ l, (R.val l k : ℂ) • fermionAnnihilation l (fermionSecondQuantization R ψ) :=
  (fermionSecondQuantization_implements R).passive_annihilation k ψ

/-- On creation words, second quantization replaces each creation direction
by its rotated one-particle vector. This is the exterior-power action. -/
theorem fermionSecondQuantization_creationWord (R : FermionModeRotation m)
    (ks : List (Fin m)) :
    fermionSecondQuantization R (fermionCreationWord ks) =
      ks.foldr (fun k ψ => ∑ l, (R.val l k : ℂ) • fermionCreation l ψ)
        (fermionVacuum m) := by
  induction ks with
  | nil => exact fermionSecondQuantization_vacuum R
  | cons k ks ih =>
    change fermionSecondQuantization R (fermionCreation k (fermionCreationWord ks)) = _
    rw [fermionSecondQuantization_creation, ih]
    rfl

private theorem continuous_fermionSecondQuantization_word (ks : List (Fin m)) :
    Continuous (fun R : FermionModeRotation m =>
      fermionSecondQuantization R (fermionCreationWord ks)) := by
  induction ks with
  | nil => simpa [fermionCreationWord] using
      (continuous_const : Continuous (fun _ : FermionModeRotation m => fermionVacuum m))
  | cons k ks ih =>
    change Continuous (fun R : FermionModeRotation m =>
      fermionSecondQuantization R (fermionCreation k (fermionCreationWord ks)))
    simp only [fermionSecondQuantization_creation]
    apply continuous_finsetSum
    intro l _
    have hc : Continuous (fun R : FermionModeRotation m => (R.val l k : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply k).comp ((continuous_apply l).comp continuous_subtype_val))
    have hv := (fermionCreation l).continuous_of_finiteDimensional.comp ih
    apply (hc.smul hv).congr
    intro R
    rfl

/-- Second quantization is strongly continuous, including the vacuum sector. -/
theorem continuous_fermionSecondQuantization_orbit (ψ : HF m) :
    Continuous (fun R : FermionModeRotation m => fermionSecondQuantization R ψ) := by
  classical
  have hψ : ψ = ∑ x : Qm m, ψ x • EuclideanSpace.single x (1 : ℂ) := by
    ext x
    simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply, smul_eq_mul]
  rw [hψ]
  simp only [map_sum, map_smul]
  apply continuous_finsetSum
  intro x _
  rw [← fermionCreationWord_occupiedModes x]
  apply ((continuous_fermionSecondQuantization_word (occupiedModes x)).const_smul (ψ x)).congr
  intro R
  rfl

end
end GaussianTesting
