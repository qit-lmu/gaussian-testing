module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-!
# Compactness of the special orthogonal group

The standard matrix topology makes the copy-rotation group a compact
topological group, as required by the unitary decomposition in Theorem 4.1.
-/

namespace GaussianTesting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

instance specialOrthogonal_isTopologicalGroup :
    IsTopologicalGroup (Matrix.specialOrthogonalGroup n ℝ) where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun O : Matrix.specialOrthogonalGroup n ℝ => (O.val)ᵀ)
    exact continuous_subtype_val.matrix_transpose

theorem specialOrthogonal_isClosed :
    IsClosed (Matrix.specialOrthogonalGroup n ℝ : Set (Matrix n n ℝ)) := by
  simp_rw [show (Matrix.specialOrthogonalGroup n ℝ : Set (Matrix n n ℝ)) =
      {A | A * Aᵀ = 1 ∧ A.det = 1} from by
        ext A
        rw [SetLike.mem_coe, Matrix.mem_specialOrthogonalGroup_iff,
          Matrix.mem_orthogonalGroup_iff]
        rfl]
  exact (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose)
    continuous_const).inter (isClosed_eq continuous_id.matrix_det continuous_const)

theorem specialOrthogonal_isCompact :
    IsCompact (Matrix.specialOrthogonalGroup n ℝ : Set (Matrix n n ℝ)) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).matrix.of_isClosed_subset
    specialOrthogonal_isClosed
  intro A hA
  have horth : A * Aᵀ = 1 := (Matrix.mem_orthogonalGroup_iff n ℝ).mp hA.1
  intro i j
  have hrow : ∑ k, A i k ^ 2 = 1 := by
    simpa [Matrix.mul_apply, pow_two] using congrArg (fun M : Matrix n n ℝ => M i i) horth
  have hentry : A i j ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ k, A i k ^ 2 := Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ = 1 := hrow
  exact ⟨by nlinarith, by nlinarith⟩

instance specialOrthogonal_compactSpace :
    CompactSpace (Matrix.specialOrthogonalGroup n ℝ) :=
  isCompact_iff_compactSpace.mp specialOrthogonal_isCompact

end GaussianTesting
