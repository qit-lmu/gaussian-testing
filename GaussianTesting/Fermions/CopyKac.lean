module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CopyRepresentation
public import GaussianTesting.Fermions.CopyRotationAxis
public import GaussianTesting.Fermions.ExteriorOccupation

@[expose] public section

/-!
# The Kac identification in Theorem 5.2

The actual second-quantized copy action has the manuscript's parity-string
generators. Its three axis-fixed projections are precisely the pair tests.
Theorem 4.1 therefore gives the complex spectral inclusion for their mean.
-/

namespace GaussianTesting

noncomputable section

/-- The three axis-fixed spaces of `Γ∧(R ⊗ I_m)` are the pair-test kernels. -/
theorem fermion_copy_axis_fixed (m : ℕ) :
    UnitaryRepresentation.fixedSubspace (fermionCopyRepresentation m) (SO3.axisSubgroups 0) =
      LinearMap.ker (p23 (lambdaF m)) ∧
    UnitaryRepresentation.fixedSubspace (fermionCopyRepresentation m) (SO3.axisSubgroups 1) =
      LinearMap.ker (p13 (lambdaF m)) ∧
    UnitaryRepresentation.fixedSubspace (fermionCopyRepresentation m) (SO3.axisSubgroups 2) =
      LinearMap.ker (p12 (lambdaF m)) :=
  fermion_copyRepresentation_axis_fixed (fermionCopyRepresentation m)
    continuous_fermionCopyRepresentation_orbit fermionCopyRepresentation_majorana
    fermionCopyRepresentation_vacuum

/-- The exact identity `S = T_π` in the manuscript proof of Theorem 5.2. -/
theorem fermion_Sop_eq_kacAverage (m : ℕ) :
    (Sop (PF m)).toContinuousLinearMap = SO3.kacAverage (fermionCopyRepresentation m) := by
  have h := fermion_kacAverage_eq_of_majorana_action (fermionCopyRepresentation m)
    continuous_fermionCopyRepresentation_orbit fermionCopyRepresentation_majorana
    fermionCopyRepresentation_vacuum
  apply ContinuousLinearMap.coe_injective
  exact h.symm

/-- Theorem 4.1 applied to the manuscript's actual second-quantized action. -/
theorem fermionic_spectrum_subset (m : ℕ) :
    spectrum ℂ (Sop (PF m)).toContinuousLinearMap ⊆
      Complex.ofReal '' Set.Icc 0 (7 / 12 : ℝ) ∪ {1} := by
  rw [fermion_Sop_eq_kacAverage]
  exact SO3.kacAverage_spectrum_subset (fermionCopyRepresentation m)
    continuous_fermionCopyRepresentation_orbit

end
end GaussianTesting
