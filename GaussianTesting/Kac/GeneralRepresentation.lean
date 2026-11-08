module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.GroupAverage
public import GaussianTesting.Kac.SO3Representation
public import GaussianTesting.Kac.SO3Topology

@[expose] public section

/-!+# The Kac bound for arbitrary unitary SO(3) representations

This is the arbitrary-representation assertion of manuscript Theorem 4.1.
Compact-group complete reducibility gives a dense span of finite-dimensional
invariant subspaces. On each such subspace, the axis-invariant projections are
the kernel projections of the angular-momentum generators, so the existing
irreducible Gram calculation applies. The uniform quadratic-form inequality
then passes to the whole Hilbert space by continuity.

The separate assertion that the spherical Kac walk attains the eigenvalue
`7/12` is not part of this theorem.
-/

namespace GaussianTesting.SO3

open UnitaryRepresentation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The manuscript's Kac operator: the mean of the three axis-invariant
orthogonal projections of a unitary SO(3) representation. -/
def kacAverage (π : Group →* E ≃ₗᵢ[ℂ] E) : E →L[ℂ] E :=
  groupKacAverage π axisSubgroups

/-- **Theorem 4.1, arbitrary-representation spectral bound.** Every strongly
continuous unitary SO(3) representation has its Kac spectrum in
`[0, 7/12] ∪ {1}`, without finite-dimensional or separability assumptions. -/
theorem kacAverage_spectrum_subset
    (π : Group →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ v : E, Continuous (fun g => π g v)) :
    spectrum ℂ (kacAverage π) ⊆ Complex.ofReal '' Set.Icc 0 (7 / 12 : ℝ) ∪ {1} := by
  apply groupKacAverage_spectrum_of_finite π hπ axisSubgroups (7 / 12)
  intro U hU _ x
  obtain ⟨J, hx, hy, hz⟩ := exists_angularMomentum (restrict π U hU)
    (continuous_restrict_orbit π hπ U hU)
  exact groupKacAverage_gap_of_angularMomentum (restrict π U hU) axisSubgroups J hx hy hz x

end
end GaussianTesting.SO3
