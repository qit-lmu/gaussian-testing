module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import GaussianTesting.Kac.CompactAverage
public import GaussianTesting.Kac.UnitaryRepresentation

@[expose] public section

/-!
# Finite-dimensional summands of compact unitary representations

A nonzero compact self-adjoint operator commuting with a unitary
representation has a nonzero finite-dimensional invariant eigenspace.
Applied to the Haar average of a rank-one operator, this is the analytic
step in the compact-group decomposition used in Theorem 4.1.
-/

namespace GaussianTesting.UnitaryRepresentation

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {G E : Type*} [Group G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A compact self-adjoint intertwiner yields a nonzero finite-dimensional
invariant subspace, by taking an eigenspace with nonzero eigenvalue. -/
theorem exists_finiteDimensional_invariant_of_compact_commuting
    (π : G →* E ≃ₗᵢ[ℂ] E) (A : E →L[ℂ] E)
    (hc : IsCompactOperator A) (hs : A.IsSymmetric) (hne : A ≠ 0)
    (hcomm : ∀ g x, A (π g x) = π g (A x)) :
    ∃ U : Submodule ℂ E, U ≠ ⊥ ∧ FiniteDimensional ℂ U ∧
      Invariant π U := by
  have hnonzero : ¬ ∀ μ : ℂ, Module.End.HasEigenvalue A.toLinearMap μ → μ = 0 := by
    intro h
    exact hne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hc hs).mp h)
  push Not at hnonzero
  obtain ⟨μ, hμ, hμ0⟩ := hnonzero
  refine ⟨Module.End.eigenspace A.toLinearMap μ, hμ,
    ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ0, ?_⟩
  intro g x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change A x = μ • x at hx
  change A (π g x) = μ • π g x
  rw [hcomm, hx, map_smul]

/-- An invariant subspace is irreducible when it is nonzero and has no
proper nonzero invariant subspace. -/
def Irreducible (π : G →* E ≃ₗᵢ[ℂ] E) (U : Submodule ℂ E) : Prop :=
  U ≠ ⊥ ∧ ∀ V : Submodule ℂ E, V ≤ U → Invariant π V → V = ⊥ ∨ V = U

omit [CompleteSpace E] in
/-- A nonzero finite-dimensional invariant subspace contains an irreducible
invariant subspace, by minimizing its positive dimension. -/
theorem exists_irreducible_le (π : G →* E ≃ₗᵢ[ℂ] E)
    (U : Submodule ℂ E) [FiniteDimensional ℂ U]
    (hU : Invariant π U) (hUne : U ≠ ⊥) :
    ∃ V : Submodule ℂ E, V ≤ U ∧ Invariant π V ∧
      FiniteDimensional ℂ V ∧ Irreducible π V := by
  classical
  let p : ℕ → Prop := fun n => ∃ V : Submodule ℂ E,
    V ≤ U ∧ V ≠ ⊥ ∧ Invariant π V ∧ Module.finrank ℂ V = n
  have hex : ∃ n, p n := ⟨Module.finrank ℂ U, U, le_rfl, hUne, hU, rfl⟩
  obtain ⟨V, hVU, hVne, hV, hdim⟩ := Nat.find_spec hex
  let : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVU
  refine ⟨V, hVU, hV, inferInstance, hVne, ?_⟩
  intro W hWV hW
  by_cases hWne : W = ⊥
  · exact Or.inl hWne
  · right
    apply Submodule.eq_of_le_of_finrank_le hWV
    rw [hdim]
    exact Nat.find_min' hex ⟨W, hWV.trans hVU, hWne, hW, rfl⟩

/-- The algebraic sum of the finite-dimensional invariant subspaces. -/
def finiteInvariantSpan (π : G →* E ≃ₗᵢ[ℂ] E) : Submodule ℂ E :=
  ⨆ U : {U : Submodule ℂ E // Invariant π U ∧ FiniteDimensional ℂ U}, U.val

/-- Vectors lying in a finite-dimensional invariant subspace form a subspace:
two witnesses are contained in their finite-dimensional invariant sum. -/
def finiteInvariantVectors (π : G →* E ≃ₗᵢ[ℂ] E) : Submodule ℂ E where
  carrier := {x | ∃ U : Submodule ℂ E, Invariant π U ∧ FiniteDimensional ℂ U ∧ x ∈ U}
  zero_mem' := by
    refine ⟨⊥, ?_, inferInstance, Submodule.zero_mem _⟩
    intro g x hx
    have hx0 : x = 0 := hx
    subst x
    change π g 0 = 0
    exact map_zero _
  add_mem' := by
    rintro x y ⟨U,hU,hUfd,hx⟩ ⟨V,hV,hVfd,hy⟩
    let : FiniteDimensional ℂ U := hUfd
    let : FiniteDimensional ℂ V := hVfd
    refine ⟨U ⊔ V, ?_, inferInstance, Submodule.add_mem_sup hx hy⟩
    intro g z hz
    have hle : U ⊔ V ≤ (U ⊔ V).comap (π g).toLinearMap :=
      sup_le (fun x hx => (show U ≤ U ⊔ V from le_sup_left) (hU g x hx))
        (fun x hx => (show V ≤ U ⊔ V from le_sup_right) (hV g x hx))
    exact hle hz
  smul_mem' := by
    rintro a x ⟨U,hU,hUfd,hx⟩
    exact ⟨U,hU,hUfd,U.smul_mem a hx⟩

omit [CompleteSpace E] in
theorem finiteInvariantVectors_eq_span (π : G →* E ≃ₗᵢ[ℂ] E) :
    finiteInvariantVectors π = finiteInvariantSpan π := by
  apply le_antisymm
  · rintro x ⟨U,hU,hUfd,hx⟩
    exact (le_iSup (fun U : {U : Submodule ℂ E // Invariant π U ∧ FiniteDimensional ℂ U}
      => U.val) ⟨U,hU,hUfd⟩) hx
  · apply iSup_le
    intro U x hx
    exact ⟨U.val,U.property.1,U.property.2,hx⟩

/-- The algebraic sum of the finite-dimensional irreducible invariant subspaces. -/
def irreducibleSpan (π : G →* E ≃ₗᵢ[ℂ] E) : Submodule ℂ E :=
  ⨆ U : {U : Submodule ℂ E //
    Invariant π U ∧ FiniteDimensional ℂ U ∧ Irreducible π U}, U.val

/-- The orthogonal-complement argument for complete reducibility. If every
nonzero closed invariant subspace contains a nonzero finite-dimensional
invariant subspace, the finite-dimensional irreducible subspaces span densely. -/
theorem irreducibleSpan_dense_of_finite_invariant_in_closed
    (π : G →* E ≃ₗᵢ[ℂ] E)
    (hsmall : ∀ U : Submodule ℂ E, Invariant π U → IsClosed (U : Set E) → U ≠ ⊥ →
      ∃ W : Submodule ℂ E, W ≤ U ∧ W ≠ ⊥ ∧ Invariant π W ∧ FiniteDimensional ℂ W) :
    (irreducibleSpan π).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  by_contra hne
  have hS : Invariant π (irreducibleSpan π) :=
    Invariant.iSup (fun U => U.property.1)
  obtain ⟨W, hWS, hWne, hW, hWfd⟩ :=
    hsmall (irreducibleSpan π)ᗮ hS.orthogonal
      (irreducibleSpan π).isClosed_orthogonal hne
  let : FiniteDimensional ℂ W := hWfd
  obtain ⟨V, hVW, hV, hVfd, hVir⟩ := exists_irreducible_le π W hW hWne
  have hVS : V ≤ irreducibleSpan π :=
    le_iSup_of_le ⟨V, hV, hVfd, hVir⟩ le_rfl
  have hVorth : V ≤ (irreducibleSpan π)ᗮ := hVW.trans hWS
  have hz : V = ⊥ := by
    apply le_antisymm _ bot_le
    simpa only [Submodule.inf_orthogonal_eq_bot] using le_inf hVS hVorth
  exact hVir.1 hz

/-- The corresponding dense sum of all finite-dimensional invariant subspaces,
which is convenient for extending a uniform operator inequality by continuity. -/
theorem finiteInvariantSpan_dense_of_finite_invariant_in_closed
    (π : G →* E ≃ₗᵢ[ℂ] E)
    (hsmall : ∀ U : Submodule ℂ E, Invariant π U → IsClosed (U : Set E) → U ≠ ⊥ →
      ∃ W : Submodule ℂ E, W ≤ U ∧ W ≠ ⊥ ∧ Invariant π W ∧ FiniteDimensional ℂ W) :
    (finiteInvariantSpan π).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← irreducibleSpan_dense_of_finite_invariant_in_closed π hsmall]
  apply Submodule.topologicalClosure_mono
  exact iSup_le (fun U => le_iSup_of_le ⟨U.val, U.property.1, U.property.2.1⟩ le_rfl)

theorem finiteInvariantVectors_dense_of_finite_invariant_in_closed
    (π : G →* E ≃ₗᵢ[ℂ] E)
    (hsmall : ∀ U : Submodule ℂ E, Invariant π U → IsClosed (U : Set E) → U ≠ ⊥ →
      ∃ W : Submodule ℂ E, W ≤ U ∧ W ≠ ⊥ ∧ Invariant π W ∧ FiniteDimensional ℂ W) :
    (finiteInvariantVectors π).topologicalClosure = ⊤ := by
  rw [finiteInvariantVectors_eq_span]
  exact finiteInvariantSpan_dense_of_finite_invariant_in_closed π hsmall

section CompactGroup

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
variable (π : G →* E ≃ₗᵢ[ℂ] E)
  (hπ : ∀ v : E, Continuous (fun g : G => π g v))
  (μ : Measure G) [IsProbabilityMeasure μ]
  [Measure.IsMulLeftInvariant μ] [Measure.IsOpenPosMeasure μ]

include hπ μ

/-- Restricting the Haar-average argument to any nonzero closed invariant
subspace gives a nonzero finite-dimensional invariant subspace inside it. -/
theorem exists_finiteDimensional_invariant_le
    (U : Submodule ℂ E) (hU : Invariant π U) (hclosed : IsClosed (U : Set E))
    (hUne : U ≠ ⊥) :
    ∃ W : Submodule ℂ E, W ≤ U ∧ W ≠ ⊥ ∧ Invariant π W ∧ FiniteDimensional ℂ W := by
  let : CompleteSpace U := hclosed.completeSpace_coe
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hv : (⟨u, hu⟩ : U) ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  obtain ⟨A, hc, hs, hne, hcomm⟩ := exists_compact_symmetric_commuting_ne_zero
    (restrict π U hU) (continuous_restrict_orbit π hπ U hU) μ hv
  obtain ⟨W, hWne, hWfd, hW⟩ :=
    exists_finiteDimensional_invariant_of_compact_commuting (restrict π U hU)
      A hc hs hne hcomm
  let : FiniteDimensional ℂ W := hWfd
  refine ⟨W.map U.subtype, ?_, ?_, ?_, inferInstance⟩
  · rintro x ⟨w, _, rfl⟩
    exact w.property
  · intro hzero
    apply hWne
    apply Submodule.map_injective_of_injective U.injective_subtype
    simpa only [Submodule.map_bot] using hzero
  · rintro g x ⟨w, hw, rfl⟩
    exact ⟨restrict π U hU g w, hW g w hw, rfl⟩

/-- Complete reducibility of a strongly continuous unitary representation of
a compact group: its finite-dimensional irreducible invariant subspaces span
the Hilbert space densely. -/
theorem irreducibleSpan_dense : (irreducibleSpan π).topologicalClosure = ⊤ :=
  irreducibleSpan_dense_of_finite_invariant_in_closed π
    (exists_finiteDimensional_invariant_le π hπ μ)

/-- Every vector is a limit of vectors contained in finite-dimensional
invariant subspaces. This form of compact unitary decomposition lets uniform
finite-dimensional quadratic-form bounds pass to the whole Hilbert space. -/
theorem finiteInvariantVectors_dense : (finiteInvariantVectors π).topologicalClosure = ⊤ :=
  finiteInvariantVectors_dense_of_finite_invariant_in_closed π
    (exists_finiteDimensional_invariant_le π hπ μ)

end CompactGroup

section ProbabilityHaar

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the whole compact group. -/
def probabilityHaar : Measure G :=
  Measure.haarMeasure
    (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : TopologicalSpace.PositiveCompacts G)

instance probabilityHaar_isProbabilityMeasure :
    IsProbabilityMeasure (probabilityHaar (G := G)) :=
  ⟨Measure.haarMeasure_self⟩

instance probabilityHaar_isMulLeftInvariant :
    Measure.IsMulLeftInvariant (probabilityHaar (G := G)) := by
  unfold probabilityHaar
  infer_instance

instance probabilityHaar_isOpenPosMeasure :
    Measure.IsOpenPosMeasure (probabilityHaar (G := G)) := by
  unfold probabilityHaar
  infer_instance

/-- Complete reducibility with the normalized Haar measure chosen canonically. -/
theorem irreducibleSpan_dense_haar
    (π : G →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ v : E, Continuous (fun g : G => π g v)) :
    (irreducibleSpan π).topologicalClosure = ⊤ :=
  irreducibleSpan_dense π hπ probabilityHaar

/-- Density of finite-dimensional invariant vectors, with no measure parameter. -/
theorem finiteInvariantVectors_dense_haar
    (π : G →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ v : E, Continuous (fun g : G => π g v)) :
    (finiteInvariantVectors π).topologicalClosure = ⊤ :=
  finiteInvariantVectors_dense π hπ probabilityHaar

end ProbabilityHaar

end
end GaussianTesting.UnitaryRepresentation
