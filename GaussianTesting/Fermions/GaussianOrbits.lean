module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.GaussianImplementers
public import GaussianTesting.Fermions.ParityOrbits

@[expose] public section

/-!
# The even and odd Gaussian orbits

The state classes are defined independently by the manuscript's SO(2m)
Majorana action. Plane-rotation generation and parity transitivity identify
these orbits with the existing coordinate predicate `IsGaussian`. No Gaussian
certainty or covariance-classification theorem is used.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- The Gaussian-unitary orbit of an occupation vector, including scalar phases. -/
def fermionicGaussianOrbit (x : Qm m) : Set (HF m) :=
  {ψ | ∃ U : HF m ≃ₗᵢ[ℂ] HF m, U ∈ gaussianUnitaryGroup m ∧
    U (EuclideanSpace.single x 1) = ψ}

/-- Gaussian states of a specified occupation parity. -/
def fermionicGaussianStatesOfParity (m : ℕ) (p : ℂ) : Set (HF m) :=
  {ψ | ∃ x : Qm m, occupationParity x = p ∧ ψ ∈ fermionicGaussianOrbit x}

/-- The even Gaussian orbit from Section 5. -/
def evenFermionicGaussianStates (m : ℕ) : Set (HF m) :=
  fermionicGaussianStatesOfParity m 1

/-- The odd Gaussian orbit; empty when there are no modes. -/
def oddFermionicGaussianStates (m : ℕ) : Set (HF m) :=
  fermionicGaussianStatesOfParity m (-1)

/-- The manuscript's union of its even and odd Gaussian-unitary orbits. -/
def fermionicGaussianStates (m : ℕ) : Set (HF m) :=
  evenFermionicGaussianStates m ∪ oddFermionicGaussianStates m

/-- Every occupation vector generates exactly the coordinate Gaussian states
in its own parity sector. -/
theorem mem_fermionicGaussianOrbit_iff (x : Qm m) (ψ : HF m) :
    ψ ∈ fermionicGaussianOrbit x ↔
      IsGaussian ψ ∧ parityOp ψ = occupationParity x • ψ := by
  unfold fermionicGaussianOrbit
  simp only [Set.mem_ofPred_eq, gaussianUnitaryGroup_eq_planeUnitaryGroup]
  exact exists_planeUnitary_basis_iff x ψ

/-- The orbit is independent of the occupation vector chosen in its sector. -/
theorem fermionicGaussianOrbit_eq_parityClass (x : Qm m) :
    fermionicGaussianOrbit x = fermionicGaussianStatesOfParity m (occupationParity x) := by
  ext ψ
  constructor
  · exact fun h => ⟨x, rfl, h⟩
  · rintro ⟨y, hy, hψ⟩
    rw [mem_fermionicGaussianOrbit_iff] at hψ ⊢
    simpa only [hy] using hψ

/-- The even orbit can be based at the vacuum occupation vector. -/
theorem evenFermionicGaussianStates_eq_vacuum_orbit (m : ℕ) :
    evenFermionicGaussianStates m = fermionicGaussianOrbit (fun _ => false) := by
  simpa [evenFermionicGaussianStates, occupationParity] using
    (fermionicGaussianOrbit_eq_parityClass (m := m) (fun _ => false)).symm

/-- Every odd occupation vector can serve as the base of the odd orbit. -/
theorem oddFermionicGaussianStates_eq_orbit (x : Qm m)
    (hx : occupationParity x = -1) :
    oddFermionicGaussianStates m = fermionicGaussianOrbit x := by
  simpa only [hx, oddFermionicGaussianStates] using
    (fermionicGaussianOrbit_eq_parityClass x).symm

/-- The two independently defined SO(2m) orbits are precisely `IsGaussian`. -/
theorem mem_fermionicGaussianStates_iff (ψ : HF m) :
    ψ ∈ fermionicGaussianStates m ↔ IsGaussian ψ := by
  constructor
  · rintro (⟨x, hx, hψ⟩ | ⟨x, hx, hψ⟩) <;>
      exact ((mem_fermionicGaussianOrbit_iff x ψ).mp hψ).1
  · intro hψ
    obtain ⟨U, hU, x, hx⟩ := (isGaussian_iff_exists_planeUnitary_basis ψ).mp hψ
    have horbit : ψ ∈ fermionicGaussianOrbit x :=
      ⟨U, planeUnitaryGroup_le_gaussianUnitaryGroup hU, hx⟩
    rcases neg_one_pow_eq_or ℂ (Finset.univ.filter fun k => x k).card with hp | hp
    · exact Or.inl ⟨x, hp, horbit⟩
    · exact Or.inr ⟨x, hp, horbit⟩

theorem fermionicGaussianStates_eq_isGaussian (m : ℕ) :
    fermionicGaussianStates m = {ψ | IsGaussian ψ} := by
  ext ψ
  exact mem_fermionicGaussianStates_iff ψ

/-- The odd orbit has no base vector in the zero-mode system. -/
theorem oddFermionicGaussianStates_zero : oddFermionicGaussianStates 0 = ∅ := by
  ext ψ
  norm_num [oddFermionicGaussianStates, fermionicGaussianStatesOfParity, occupationParity]

end
end GaussianTesting
