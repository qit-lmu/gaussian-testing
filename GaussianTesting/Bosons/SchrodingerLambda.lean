module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerCore
public import GaussianTesting.Bosons.SchrodingerDerivative
public import GaussianTesting.Bosons.RotationGraphClosure
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

/-!
# The graph-closed Schrödinger generator and its acceptance projection

The initial domain consists of finite linear combinations of the manuscript's
creation-generated number vectors in actual Lebesgue `L²`. Its generator is
the stated creation-annihilation expression, and its domain is enlarged by
taking the actual graph closure. The integrated rotation identity proves
closability and proves that every rotation fixes the kernel of the closure.
-/

namespace GaussianTesting

open MeasureTheory

noncomputable section

/-- The manuscript's `Λ` on its prescribed graph-norm-closed domain, in the
actual two-copy Schrödinger Hilbert space. -/
def schrodingerLambda (m : ℕ) :
    SchrodingerSpace m →ₗ.[ℂ] SchrodingerSpace m :=
  RotationGraphClosure.closedGenerator (schrodingerFiniteFockGraph m)

/-- The graph is exactly the closure of the specified finite Fock graph. -/
theorem schrodingerLambda_graph (m : ℕ) :
    (schrodingerLambda m).graph = (schrodingerFiniteFockGraph m).topologicalClosure :=
  RotationGraphClosure.closedGenerator_graph
    (fun t => (schrodingerRotation m t).toLinearIsometry)
    (continuous_schrodingerRotation m) (schrodingerRotation_zero m)
    (schrodingerFiniteFockGraph m) (schrodingerFiniteFockGraph_hasDerivAt m)

theorem schrodingerLambda_isClosed (m : ℕ) : (schrodingerLambda m).IsClosed := by
  rw [LinearPMap.IsClosed, schrodingerLambda_graph]
  exact (schrodingerFiniteFockGraph m).isClosed_topologicalClosure

/-- The initial finite-core operator, before taking its graph closure. -/
def schrodingerFiniteLambda (m : ℕ) :
    SchrodingerSpace m →ₗ.[ℂ] SchrodingerSpace m :=
  (schrodingerFiniteFockGraph m).toLinearPMap

theorem schrodingerFiniteLambda_graph (m : ℕ) :
    (schrodingerFiniteLambda m).graph = schrodingerFiniteFockGraph m := by
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hzero
  exact RotationGraphClosure.singleValued
    (fun t => (schrodingerRotation m t).toLinearIsometry)
    (continuous_schrodingerRotation m) (schrodingerRotation_zero m)
    (schrodingerFiniteFockGraph m) (schrodingerFiniteFockGraph_hasDerivAt m)
    z ((schrodingerFiniteFockGraph m).le_topologicalClosure hz) hzero

/-- The initial domain is precisely the realization of the finite Fock span. -/
theorem schrodingerFiniteLambda_mem_domain (m : ℕ) (f : SchrodingerSpace m) :
    f ∈ (schrodingerFiniteLambda m).domain ↔
      ∃ p ∈ finiteFockPolynomialCore m, polynomialGaussian p = f := by
  rw [← LinearPMap.graph_map_fst_eq_domain, schrodingerFiniteLambda_graph]
  constructor
  · rintro ⟨z, ⟨p, rfl⟩, hz⟩
    exact ⟨p.1, p.2, hz⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(polynomialGaussian p, polynomialGaussian (polynomialLambda m p)),
      ⟨⟨p, hp⟩, rfl⟩, rfl⟩

theorem schrodingerFiniteLambda_isClosable (m : ℕ) :
    (schrodingerFiniteLambda m).IsClosable := by
  refine ⟨schrodingerLambda m, ?_⟩
  rw [schrodingerFiniteLambda_graph, schrodingerLambda_graph]

/-- The physical operator is the graph closure, not a separately chosen extension. -/
theorem schrodingerLambda_eq_closure (m : ℕ) :
    schrodingerLambda m = (schrodingerFiniteLambda m).closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [schrodingerLambda_graph,
    ← (schrodingerFiniteLambda_isClosable m).graph_closure_eq_closure_graph,
    schrodingerFiniteLambda_graph]

theorem schrodingerLambda_hasCore (m : ℕ) :
    (schrodingerLambda m).HasCore (schrodingerFiniteLambda m).domain := by
  rw [schrodingerLambda_eq_closure]
  exact (schrodingerFiniteLambda m).closureHasCore

/-- Every vector in the closed kernel is fixed by the actual wavefunction rotations. -/
theorem schrodingerRotation_fixed_of_mem_kernel (m : ℕ)
    {f : SchrodingerSpace m} (hf : f ∈ (schrodingerLambda m).ker) (θ : ℝ) :
    schrodingerRotation m θ f = f :=
  RotationGraphClosure.fixed_of_mem_ker
    (fun t => (schrodingerRotation m t).toLinearIsometry)
    (continuous_schrodingerRotation m) (schrodingerRotation_zero m)
    (schrodingerFiniteFockGraph m) (schrodingerFiniteFockGraph_hasDerivAt m) hf θ

theorem schrodingerLambda_kernel_isClosed (m : ℕ) :
    IsClosed ((schrodingerLambda m).ker : Set (SchrodingerSpace m)) := by
  have he : ((schrodingerLambda m).ker : Set (SchrodingerSpace m)) =
      {f | (f, 0) ∈ (schrodingerLambda m).graph} := by
    ext f
    change f ∈ (schrodingerLambda m).ker ↔ (f, 0) ∈ (schrodingerLambda m).graph
    constructor
    · intro hf
      obtain ⟨x, hx, hy⟩ := (schrodingerLambda m).mem_ker_iff.mp hf
      exact (schrodingerLambda m).mem_graph_iff.mpr ⟨x, hx.symm, hy⟩
    · intro hf
      obtain ⟨x, hx, hy⟩ := (schrodingerLambda m).mem_graph_iff.mp hf
      exact (schrodingerLambda m).mem_ker_iff.mpr ⟨x, hx.symm, hy⟩
  rw [he]
  exact (schrodingerLambda_isClosed m).preimage (continuous_id.prodMk continuous_const)

instance schrodingerLambda_kernel_completeSpace (m : ℕ) :
    CompleteSpace (schrodingerLambda m).ker :=
  (schrodingerLambda_kernel_isClosed m).isComplete.completeSpace_coe

/-- The manuscript's accepting projection `P₀ = proj(ker Λ)` on wavefunctions. -/
def schrodingerP0 (m : ℕ) : SchrodingerSpace m →L[ℂ] SchrodingerSpace m :=
  (schrodingerLambda m).ker.starProjection

theorem schrodingerP0_symmetric (m : ℕ) (x y : SchrodingerSpace m) :
    inner ℂ (schrodingerP0 m x) y = inner ℂ x (schrodingerP0 m y) :=
  Submodule.inner_starProjection_left_eq_right _ x y

theorem schrodingerP0_idempotent (m : ℕ) (x : SchrodingerSpace m) :
    schrodingerP0 m (schrodingerP0 m x) = schrodingerP0 m x := by
  exact Submodule.starProjection_eq_self_iff.mpr
    ((schrodingerLambda m).ker.starProjection_apply_mem x)

/-- The fixed-space assertion used in the first line of Lemma 6.2's proof. -/
theorem schrodingerRotation_P0 (m : ℕ) (θ : ℝ) (x : SchrodingerSpace m) :
    schrodingerRotation m θ (schrodingerP0 m x) = schrodingerP0 m x :=
  schrodingerRotation_fixed_of_mem_kernel m
    ((schrodingerLambda m).ker.starProjection_apply_mem x) θ

end
end GaussianTesting
