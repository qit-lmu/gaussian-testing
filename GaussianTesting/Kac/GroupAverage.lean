module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.UnitaryRepresentation
public import GaussianTesting.Kac.CompactDecomposition
public import GaussianTesting.Kac.KacWalk
public import GaussianTesting.GradientFlow.Spectral

@[expose] public section

/-!
# The Kac average of subgroup-invariant projections

Theorem 4.1 uses three subgroups of the rotation group. Their fixed spaces
are closed even in an infinite-dimensional Hilbert space. Restricting a unitary
representation to a closed invariant subspace commutes with these projections.
Consequently the same uniform polynomial bound on a dense family of finite
invariant subspaces gives the spectral bound on the full Hilbert space.
-/

namespace GaussianTesting.UnitaryRepresentation

open scoped InnerProductSpace

noncomputable section

variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem Invariant.starProjection_commutes {π : G →* E ≃ₗᵢ[ℂ] E}
    {U : Submodule ℂ E} [CompleteSpace U] (hU : Invariant π U) (g : G) (x : E) :
    U.starProjection (π g x) = π g (U.starProjection x) := by
  apply U.eq_starProjection_of_mem_orthogonal (hU g _ (U.starProjection_apply_mem x))
  rw [← map_sub]
  exact hU.orthogonal g _ (U.sub_starProjection_mem_orthogonal x)

/-- The ambient fixed-space projection agrees with the restricted one. -/
theorem fixedProjection_restrict (π : G →* E ≃ₗᵢ[ℂ] E) (K : Subgroup G)
    (U : Submodule ℂ E) [CompleteSpace U] (hU : Invariant π U) (x : U) :
    (fixedSubspace π K).starProjection (x : E) =
      ((fixedSubspace (restrict π U hU) K).starProjection x : E) := by
  let F := fixedSubspace (restrict π U hU) K
  apply (fixedSubspace π K).eq_starProjection_of_mem_of_inner_eq_zero
  · intro g hg
    have h := F.starProjection_apply_mem x
    exact congrArg Subtype.val (h g hg)
  · intro w hw
    let u : U := ⟨U.starProjection w, U.starProjection_apply_mem w⟩
    have hu : u ∈ F := by
      intro g hg
      apply Subtype.ext
      change π g (U.starProjection w) = U.starProjection w
      rw [← hU.starProjection_commutes, hw g hg]
    have h₁ : ⟪(x : E) - (F.starProjection x : E), (u : E)⟫_ℂ = 0 :=
      F.starProjection_inner_eq_zero x u hu
    have h₂ : ⟪(x : E) - (F.starProjection x : E), w - (u : E)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (U.sub_mem x.property (F.starProjection x).property)
        (U.sub_starProjection_mem_orthogonal w)
    have he : w = (u : E) + (w - (u : E)) := by abel
    rw [he, inner_add_right, h₁, h₂, add_zero]

/-- The average in Eq. (4.1), for three specified axis subgroups. -/
def groupKacAverage (π : G →* E ≃ₗᵢ[ℂ] E) (K : Fin 3 → Subgroup G) : E →L[ℂ] E :=
  (3 : ℂ)⁻¹ • ((fixedSubspace π (K 0)).starProjection +
    (fixedSubspace π (K 1)).starProjection + (fixedSubspace π (K 2)).starProjection)

theorem groupKacAverage_restrict (π : G →* E ≃ₗᵢ[ℂ] E) (K : Fin 3 → Subgroup G)
    (U : Submodule ℂ E) [CompleteSpace U] (hU : Invariant π U) (x : U) :
    groupKacAverage π K (x : E) = (groupKacAverage (restrict π U hU) K x : E) := by
  simp only [groupKacAverage, smul_apply, add_apply,
    Submodule.coe_smul, Submodule.coe_add, fixedProjection_restrict π _ U hU x]

theorem groupKacAverage_norm_le_one (π : G →* E ≃ₗᵢ[ℂ] E) (K : Fin 3 → Subgroup G) :
    ‖groupKacAverage π K‖ ≤ 1 := by
  let P := fun i => (fixedSubspace π (K i)).starProjection
  have h0 := (fixedSubspace π (K 0)).starProjection_norm_le
  have h1 := (fixedSubspace π (K 1)).starProjection_norm_le
  have h2 := (fixedSubspace π (K 2)).starProjection_norm_le
  rw [groupKacAverage, norm_smul, norm_inv]
  norm_num only [Complex.norm_ofNat]
  linarith [norm_add_le (P 0) (P 1), norm_add_le (P 0 + P 1) (P 2)]

open scoped ComplexOrder in
theorem groupKacAverage_nonneg (π : G →* E ≃ₗᵢ[ℂ] E) (K : Fin 3 → Subgroup G) :
    0 ≤ groupKacAverage π K := by
  have hp (i : Fin 3) : (fixedSubspace π (K i)).starProjection.IsPositive := by
    refine ⟨(fixedSubspace π (K i)).starProjection_isSymmetric, fun x => ?_⟩
    change 0 ≤ (⟪(fixedSubspace π (K i)).starProjection x, x⟫_ℂ).re
    exact (fixedSubspace π (K i)).re_inner_starProjection_nonneg x
  have hc : 0 ≤ (3 : ℂ)⁻¹ := by simp
  exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (((hp 0).add (hp 1)).add (hp 2) |>.smul_of_nonneg hc)

/-- A uniform polynomial bound passes from a dense set of vectors to all
vectors, and hence gives the complex spectral inclusion. -/
theorem groupKacAverage_spectrum_of_dense (π : G →* E ≃ₗᵢ[ℂ] E)
    (K : Fin 3 → Subgroup G) (α : ℝ) {D : Set E} (hD : Dense D)
    (hgap : ∀ x ∈ D, 0 ≤ (⟪x, groupKacAverage π K (groupKacAverage π K x)⟫_ℂ -
      (1 + (α : ℂ)) * ⟪x, groupKacAverage π K x⟫_ℂ + (α : ℂ) * ⟪x, x⟫_ℂ).re) :
    spectrum ℂ (groupKacAverage π K) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1} := by
  apply (spectrum_gap_iff_quadraticForm_nonneg (groupKacAverage_nonneg π K)
    (groupKacAverage_norm_le_one π K) α).mpr
  have hc : IsClosed {x : E | 0 ≤
      (⟪x, groupKacAverage π K (groupKacAverage π K x)⟫_ℂ -
        (1 + (α : ℂ)) * ⟪x, groupKacAverage π K x⟫_ℂ + (α : ℂ) * ⟪x, x⟫_ℂ).re} :=
    isClosed_le continuous_const (by fun_prop)
  exact fun x => hc.closure_subset_iff.mpr hgap (hD x)

/-- On a finite-dimensional representation, identifying the three fixed spaces
with the angular-momentum kernels identifies the two versions of the Kac bound. -/
theorem groupKacAverage_gap_of_angularMomentum [FiniteDimensional ℂ E]
    (π : G →* E ≃ₗᵢ[ℂ] E) (K : Fin 3 → Subgroup G) (J : AngularMomentum E)
    (hx : fixedSubspace π (K 0) = LinearMap.ker J.Jx)
    (hy : fixedSubspace π (K 1) = LinearMap.ker J.Jy)
    (hz : fixedSubspace π (K 2) = LinearMap.ker J.Jz) (x : E) :
    0 ≤ (⟪x, groupKacAverage π K (groupKacAverage π K x)⟫_ℂ -
      (1 + ((7 / 12 : ℝ) : ℂ)) * ⟪x, groupKacAverage π K x⟫_ℂ +
      ((7 / 12 : ℝ) : ℂ) * ⟪x, x⟫_ℂ).re := by
  have hT : (groupKacAverage π K).toLinearMap = kacT J := by
    simp only [groupKacAverage, kacT, hx, hy, hz]
    rfl
  have h := kacT_gap J x
  rw [← hT] at h
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul, inner_sub_right, inner_smul_right] at h
  change 0 ≤ (⟪x, groupKacAverage π K (groupKacAverage π K x)⟫_ℂ -
    ⟪x, groupKacAverage π K x⟫_ℂ - ((7 / 12 : ℝ) : ℂ) *
    (⟪x, groupKacAverage π K x⟫_ℂ - ⟪x, x⟫_ℂ)).re at h
  convert h using 1
  congr 1
  ring

/-- Uniform finite-dimensional bounds extend to a strongly continuous unitary
representation of a compact group. The dense finite-dimensional subspaces
come from compact-group complete reducibility. -/
theorem groupKacAverage_spectrum_of_finite
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (π : G →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ x : E, Continuous (fun g => π g x))
    (K : Fin 3 → Subgroup G) (α : ℝ)
    (hfinite : ∀ (U : Submodule ℂ E) (hU : Invariant π U) [FiniteDimensional ℂ U]
      (x : U), 0 ≤
        (⟪x, groupKacAverage (restrict π U hU) K
          (groupKacAverage (restrict π U hU) K x)⟫_ℂ -
        (1 + (α : ℂ)) * ⟪x, groupKacAverage (restrict π U hU) K x⟫_ℂ +
        (α : ℂ) * ⟪x, x⟫_ℂ).re) :
    spectrum ℂ (groupKacAverage π K) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1} := by
  apply groupKacAverage_spectrum_of_dense π K α
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (finiteInvariantVectors_dense_haar π hπ))
  rintro x ⟨U, hU, hfd, hx⟩
  let : FiniteDimensional ℂ U := hfd
  have h := hfinite U hU ⟨x, hx⟩
  change 0 ≤ (⟪x, (groupKacAverage (restrict π U hU) K
      (groupKacAverage (restrict π U hU) K ⟨x, hx⟩) : E)⟫_ℂ -
    (1 + (α : ℂ)) * ⟪x, (groupKacAverage (restrict π U hU) K ⟨x, hx⟩ : E)⟫_ℂ +
    (α : ℂ) * ⟪x, x⟫_ℂ).re at h
  simpa only [← groupKacAverage_restrict π K U hU] using h

end
end GaussianTesting.UnitaryRepresentation
