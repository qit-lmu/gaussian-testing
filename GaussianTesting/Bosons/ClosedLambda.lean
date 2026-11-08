module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.KernelCore
public import GaussianTesting.Bosons.ModesC
public import Mathlib.Topology.Algebra.Module.LinearPMap

@[expose] public section

/-!
# The closed bosonic generator and its kernel projection

The manuscript's finite Fock core is the space of finitely supported number-basis
coefficients. We take the actual closure of the graph of `lambdaB` on that core,
prove that this closed relation is an operator, and identify its kernel projection
with `P0B`. `SchrodingerFockPair.lean` transports this graph closure and its
kernel projection to the physical Schrödinger realization.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The completed two-copy number-basis Fock space. -/
abbrev FockB2 (m : ℕ) := lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2

variable {m : ℕ}

/-- The finite two-copy Fock core embedded as a complex linear map. -/
def embedFA2Linear (m : ℕ) : FA2 m →ₗ[ℂ] FockB2 m where
  toFun := embedFA2
  map_add' := embedFA2_add
  map_smul' := embedFA2_smul

private lemma blockProj_add (f g : FockB2 m) (n : ℕ) :
    blockProj degB2 (f + g) n = blockProj degB2 f n + blockProj degB2 g n := rfl

private lemma blockProj_smul (c : ℂ) (f : FockB2 m) (n : ℕ) :
    blockProj degB2 (c • f) n = c • blockProj degB2 f n := rfl

private lemma blockProj_zero (n : ℕ) :
    blockProj degB2 (0 : FockB2 m) n = 0 := rfl

private lemma continuous_blockProj (n : ℕ) :
    Continuous (fun f : FockB2 m => blockProj degB2 f n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : {p // degB2 (m := m) p = n} => ℂ)).comp
  apply continuous_pi
  intro p
  exact (lp.lipschitzWith_one_eval 2 p.1).continuous

/-- Restriction to a particle-number block commutes with the finite-core generator. -/
lemma blockProj_embedFA2_lambdaB (f : FA2 m) (n : ℕ) :
    blockProj degB2 (embedFA2 (lambdaB m f)) n =
      lambdaBlock m n (blockProj degB2 (embedFA2 f) n) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [show embedFA2 (0 : FA2 m) = 0 from map_zero (embedFA2Linear m),
      blockProj_zero]
  | add f g hf hg => simp only [map_add, embedFA2_add, blockProj_add, hf, hg]
  | single p c =>
    by_cases hp : degB2 p = n
    · have hs : IsHomog2 n (Finsupp.single p c) := by
        intro q hq
        obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hq
        exact hp
      exact (toBlock2_homogToBlock2 (conservesDeg2_lambdaB m) hs).symm
    · have hin : blockProj degB2 (embedFA2 (Finsupp.single p c)) n = 0 := by
        ext q
        change Finsupp.single p c q.1 = 0
        exact Finsupp.single_eq_of_ne (fun he => hp (he ▸ q.2))
      rw [hin, map_zero]
      ext q
      change lambdaB m (Finsupp.single p c) q.1 = 0
      rw [← Finsupp.smul_single_one p c, map_smul, Finsupp.smul_apply]
      have hz : lambdaB m (Finsupp.single p 1) q.1 = 0 := by
        by_contra h
        exact hp ((conservesDeg2_lambdaB m p q.1
          (Finsupp.mem_support_iff.mpr h)).symm.trans q.2)
      rw [hz, smul_zero]

/-- The graph of `Λ` on the finite Fock core. -/
def lambdaFiniteGraph (m : ℕ) : Submodule ℂ (FockB2 m × FockB2 m) :=
  LinearMap.range ((embedFA2Linear m).prod
    ((embedFA2Linear m).comp (lambdaB m)))

/-- The actual graph closure prescribed in the manuscript. -/
def lambdaClosedGraph (m : ℕ) : Submodule ℂ (FockB2 m × FockB2 m) :=
  (lambdaFiniteGraph m).topologicalClosure

lemma mem_lambdaFiniteGraph (f : FA2 m) :
    (embedFA2 f, embedFA2 (lambdaB m f)) ∈ lambdaFiniteGraph m := ⟨f, rfl⟩

/-- Every point of the closed graph satisfies the finite particle-block equations. -/
theorem lambdaClosedGraph_blocks {z : FockB2 m × FockB2 m}
    (hz : z ∈ lambdaClosedGraph m) (n : ℕ) :
    blockProj degB2 z.2 n = lambdaBlock m n (blockProj degB2 z.1 n) := by
  have hc : IsClosed {z : FockB2 m × FockB2 m |
      blockProj degB2 z.2 n = lambdaBlock m n (blockProj degB2 z.1 n)} :=
    isClosed_eq ((continuous_blockProj n).comp continuous_snd)
      ((lambdaBlock m n).continuous_of_finiteDimensional.comp
        ((continuous_blockProj n).comp continuous_fst))
  apply closure_minimal (s := (lambdaFiniteGraph m : Set _)) ?_ hc hz
  rintro z ⟨f, rfl⟩
  exact blockProj_embedFA2_lambdaB f n

private lemma lambdaClosedGraph_singleValued (z : FockB2 m × FockB2 m)
    (hz : z ∈ lambdaClosedGraph m) (hzero : z.1 = 0) : z.2 = 0 := by
  apply lp.ext
  funext p
  have hb := lambdaClosedGraph_blocks hz (degB2 p)
  rw [hzero, blockProj_zero, map_zero] at hb
  exact congrArg (fun v : BlockSp (degB2 (m := m)) (degB2 p) => v ⟨p, rfl⟩) hb

/-- `Λ` with the domain obtained by closing its finite Fock core in graph norm. -/
def closedLambdaB (m : ℕ) : FockB2 m →ₗ.[ℂ] FockB2 m :=
  (lambdaClosedGraph m).toLinearPMap

/-- The operator graph is exactly the closure, with no additional domain assumption. -/
theorem closedLambdaB_graph (m : ℕ) :
    (closedLambdaB m).graph = (lambdaFiniteGraph m).topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ lambdaClosedGraph_singleValued

theorem closedLambdaB_isClosed (m : ℕ) : (closedLambdaB m).IsClosed := by
  rw [LinearPMap.IsClosed, closedLambdaB_graph]
  exact (lambdaFiniteGraph m).isClosed_topologicalClosure

/-- The algebraic finite Fock generator, viewed as a densely defined operator. -/
def finiteLambdaB (m : ℕ) : FockB2 m →ₗ.[ℂ] FockB2 m :=
  (lambdaFiniteGraph m).toLinearPMap

lemma finiteLambdaB_graph (m : ℕ) :
    (finiteLambdaB m).graph = lambdaFiniteGraph m := by
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hzero
  exact lambdaClosedGraph_singleValued z
    ((lambdaFiniteGraph m).le_topologicalClosure hz) hzero

/-- The initial domain consists exactly of finitely supported coefficient vectors. -/
theorem finiteLambdaB_mem_domain_iff (f : FockB2 m) :
    f ∈ (finiteLambdaB m).domain ↔ ∃ g : FA2 m, embedFA2 g = f := by
  rw [← LinearPMap.graph_map_fst_eq_domain, finiteLambdaB_graph]
  constructor
  · rintro ⟨z, ⟨g, rfl⟩, hz⟩
    exact ⟨g, hz⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(embedFA2 g, embedFA2 (lambdaB m g)), mem_lambdaFiniteGraph g, rfl⟩

theorem finiteLambdaB_isClosable (m : ℕ) : (finiteLambdaB m).IsClosable := by
  refine ⟨closedLambdaB m, ?_⟩
  rw [finiteLambdaB_graph, closedLambdaB_graph]

/-- Closing the finite-core operator in graph norm gives `closedLambdaB`. -/
theorem closedLambdaB_eq_closure (m : ℕ) :
    closedLambdaB m = (finiteLambdaB m).closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [closedLambdaB_graph,
    ← (finiteLambdaB_isClosable m).graph_closure_eq_closure_graph, finiteLambdaB_graph]

/-- The specified finite Fock domain is a core of the closed operator. -/
theorem closedLambdaB_hasCore (m : ℕ) :
    (closedLambdaB m).HasCore (finiteLambdaB m).domain := by
  rw [closedLambdaB_eq_closure]
  exact (finiteLambdaB m).closureHasCore

/-- Every finite-core input belongs to the closed operator's domain. -/
theorem embedFA2_mem_closedLambdaB_domain (f : FA2 m) :
    embedFA2 f ∈ (closedLambdaB m).domain := by
  have hg : (embedFA2 f, embedFA2 (lambdaB m f)) ∈ (closedLambdaB m).graph := by
    rw [closedLambdaB_graph]
    exact (lambdaFiniteGraph m).le_topologicalClosure (mem_lambdaFiniteGraph f)
  obtain ⟨x, hx, _⟩ := (closedLambdaB m).mem_graph_iff.mp hg
  change (x : FockB2 m) = embedFA2 f at hx
  rw [← hx]
  exact x.2

/-- The closed operator retains the prescribed finite-core action. -/
theorem closedLambdaB_embedFA2 (f : FA2 m) :
    closedLambdaB m ⟨embedFA2 f, embedFA2_mem_closedLambdaB_domain f⟩ =
      embedFA2 (lambdaB m f) := by
  have hg : (embedFA2 f, embedFA2 (lambdaB m f)) ∈ (closedLambdaB m).graph := by
    rw [closedLambdaB_graph]
    exact (lambdaFiniteGraph m).le_topologicalClosure (mem_lambdaFiniteGraph f)
  obtain ⟨x, hx, hy⟩ := (closedLambdaB m).mem_graph_iff.mp hg
  have he : x = ⟨embedFA2 f, embedFA2_mem_closedLambdaB_domain f⟩ := Subtype.ext hx
  simpa [he] using hy

/-- The finite Fock core, and hence the closed generator domain, is dense. -/
theorem closedLambdaB_dense_domain (m : ℕ) :
    Dense ((closedLambdaB m).domain : Set (FockB2 m)) := by
  classical
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro x _
  rw [← (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x).tsum_eq]
  apply tsum_mem (closedLambdaB m).domain.isClosed_topologicalClosure
  intro p
  apply (closedLambdaB m).domain.le_topologicalClosure
  convert embedFA2_mem_closedLambdaB_domain (Finsupp.single p (x p)) using 1
  ext q
  simp [lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

private lemma closedLambdaB_mem_ker_iff_graph (f : FockB2 m) :
    f ∈ (closedLambdaB m).ker ↔ (f, 0) ∈ lambdaClosedGraph m := by
  change f ∈ (closedLambdaB m).ker ↔
    (f, 0) ∈ (lambdaFiniteGraph m).topologicalClosure
  rw [← closedLambdaB_graph]
  simp only [LinearPMap.mem_ker_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx.symm, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, hx.symm, hy⟩

/-- The kernel of the closed generator is exactly the blockwise algebraic kernel. -/
theorem closedLambdaB_mem_ker_iff_blocks (f : FockB2 m) :
    f ∈ (closedLambdaB m).ker ↔
      ∀ n, blockProj degB2 f n ∈ LinearMap.ker (lambdaBlock m n) := by
  rw [closedLambdaB_mem_ker_iff_graph]
  constructor
  · intro h n
    have hb := lambdaClosedGraph_blocks h n
    exact hb.symm
  · intro h
    have hf := P0B_fixed_mem_closure ((P0B_fixed_iff_blocks f).mpr h)
    have hc : IsClosed {f : FockB2 m | (f, 0) ∈ lambdaClosedGraph m} :=
      (lambdaFiniteGraph m).isClosed_topologicalClosure.preimage
        (continuous_id.prodMk continuous_const)
    apply closure_minimal (s := Set.range (fun b : {b : FA2 m // lambdaB m b = 0} =>
      embedFA2 b.1)) ?_ hc hf
    rintro _ ⟨b, rfl⟩
    apply (lambdaFiniteGraph m).le_topologicalClosure
    convert mem_lambdaFiniteGraph b.1 using 1
    rw [b.2]
    simp only [show embedFA2 (0 : FA2 m) = 0 from map_zero (embedFA2Linear m)]

/-- The previously constructed acceptance projection has exactly the closed
operator's kernel as its fixed space. -/
theorem P0B_fixed_iff_mem_closedLambdaB_ker (f : FockB2 m) :
    P0B m f = f ↔ f ∈ (closedLambdaB m).ker := by
  rw [P0B_fixed_iff_blocks, closedLambdaB_mem_ker_iff_blocks]

lemma closedLambdaB_isClosed_ker (m : ℕ) :
    IsClosed ((closedLambdaB m).ker : Set (FockB2 m)) := by
  have he : ((closedLambdaB m).ker : Set (FockB2 m)) =
      {f | (f, 0) ∈ lambdaClosedGraph m} := by
    ext f
    exact closedLambdaB_mem_ker_iff_graph f
  rw [he]
  exact (lambdaFiniteGraph m).isClosed_topologicalClosure.preimage
    (continuous_id.prodMk continuous_const)

instance closedLambdaB_kernel_completeSpace (m : ℕ) :
    CompleteSpace (closedLambdaB m).ker :=
  (closedLambdaB_isClosed_ker m).isComplete.completeSpace_coe

/-- The manuscript's orthogonal projection onto the kernel of the graph-closed
number-basis generator is exactly the existing bosonic test `P0B`. -/
theorem P0B_eq_closedLambdaB_kernelProjection (m : ℕ) :
    P0B m = (closedLambdaB m).ker.starProjection := by
  apply ContinuousLinearMap.ext
  intro f
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (P0B_fixed_iff_mem_closedLambdaB_ker _).mp
    exact DFunLike.congr_fun (P0B_isAcceptance m).idem f
  · intro w hw
    have hw' := (P0B_fixed_iff_mem_closedLambdaB_ker w).mpr hw
    rw [inner_sub_left, (P0B_isAcceptance m).symmetric, hw', sub_self]

end

end GaussianTesting
