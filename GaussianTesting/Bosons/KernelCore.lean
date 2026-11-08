module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Main

@[expose] public section

/-!
# The finite Fock core of the bosonic kernel projection

Finitely supported two-copy vectors embed into the completed Fock space.
The blockwise kernel projection `P0B` fixes exactly the vectors whose
particle-number components lie in the finite kernels, and its fixed space
is the closure of the embedded finite kernel. These facts identify the
kernel of the graph-closed generator in `ClosedLambda.lean`.
-/

namespace GaussianTesting

open Complex Finsupp

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {m : ℕ}

/-- The inclusion of finitely supported coefficient vectors into ℓ²
(two copies). -/
noncomputable def embedFA2 (f : FA2 m) :
    lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 := by
  classical
  refine ⟨fun p => f p, mem_of_summable_normSq ?_⟩
  apply summable_of_ne_finset_zero (s := f.support)
  intro p hp
  simp [Finsupp.notMem_support_iff.mp hp]

@[simp] lemma embedFA2_apply (f : FA2 m) (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    embedFA2 f p = f p := by
  rfl

lemma embedFA2_add (f g : FA2 m) :
    embedFA2 (f + g) = embedFA2 f + embedFA2 g := by
  apply lp.ext
  funext p
  simp

lemma embedFA2_smul (z : ℂ) (f : FA2 m) :
    embedFA2 (z • f) = z • embedFA2 f := by
  apply lp.ext
  funext p
  simp

/-- Membership in `im P₀`, blockwise. -/
lemma P0B_fixed_iff_blocks (F : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2) :
    P0B m F = F ↔
      ∀ n, blockProj degB2 F n ∈ LinearMap.ker (lambdaBlock m n) := by
  classical
  have happ (g : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
      (n : ℕ) :
      blockProj degB2 (P0B m g) n =
        (LinearMap.ker (lambdaBlock m n)).starProjection (blockProj degB2 g n) := by
    ext p
    obtain ⟨p, hp⟩ := p
    subst n
    rfl
  constructor
  · intro h n
    apply (LinearMap.ker (lambdaBlock m n)).starProjection_eq_self_iff.mp
    rw [← happ, h]
  · intro h
    apply lp.ext
    funext p
    have hn := (LinearMap.ker (lambdaBlock m (degB2 p))).starProjection_eq_self_iff.mpr
      (h (degB2 p))
    rw [← happ] at hn
    exact congrArg (fun v : BlockSp (degB2 (m := m)) (degB2 p) => v ⟨p, rfl⟩) hn

private lemma kernel_P0B_apply
    (x : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
    (q : (Fin m → ℕ) × (Fin m → ℕ)) {n : ℕ} (hq : degB2 q = n) :
    P0B m x q = (LinearMap.ker (lambdaBlock m n)).starProjection
      (blockProj degB2 x n) ⟨q, hq⟩ := by
  subst n
  rfl

/-- A fixed point of `P₀` is a limit of
embedded finite kernel vectors. -/
lemma P0B_fixed_mem_closure {F : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2}
    (hF : P0B m F = F) :
    F ∈ closure (Set.range (fun b : {b : FA2 m // lambdaB m b = 0} =>
      embedFA2 b.1)) := by
  classical
  let E : FA2 m →ₗ[ℂ] lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 :=
    { toFun := embedFA2, map_add' := embedFA2_add, map_smul' := embedFA2_smul }
  let K := LinearMap.range (E.comp (LinearMap.ker (lambdaB m)).subtype)
  have hr : (K : Set _) = Set.range (fun b : {b : FA2 m // lambdaB m b = 0} =>
      embedFA2 b.1) := rfl
  rw [← hr, ← Submodule.topologicalClosure_coe]
  change F ∈ K.topologicalClosure
  have hs := (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) F).map
    (P0B m) (P0B m).continuous
  rw [hF] at hs
  rw [← hs.tsum_eq]
  apply tsum_mem K.isClosed_topologicalClosure
  intro p
  apply K.le_topologicalClosure
  let n := degB2 p
  let v := (LinearMap.ker (lambdaBlock m n)).starProjection
    (blockProj degB2 (lp.single 2 p (F p)) n)
  have hv : lambdaBlock m n v = 0 :=
    LinearMap.mem_ker.mp ((LinearMap.ker (lambdaBlock m n)).starProjection_apply_mem _)
  have hb : lambdaB m (blockLift2 n v) = 0 := by
    rw [← blockLift2_toBlock2 (conservesDeg2_lambdaB m)]
    change blockLift2 n (lambdaBlock m n v) = 0
    rw [hv, map_zero]
  refine ⟨⟨blockLift2 n v, hb⟩, ?_⟩
  change embedFA2 (blockLift2 n v) = P0B m (lp.single 2 p (F p))
  apply lp.ext
  funext q
  rw [embedFA2_apply, blockLift2_apply]
  by_cases hq : degB2 q = n
  · rw [dite_eq_left hq]
    exact (kernel_P0B_apply _ q hq).symm
  · rw [dite_eq_right hq]
    have hz : blockProj degB2 (lp.single 2 p (F p)) (degB2 q) = 0 := by
      ext r
      change (lp.single 2 p (F p) : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2) r.1 = 0
      rw [lp.single_apply]
      apply Pi.single_eq_of_ne
      intro hpr
      exact hq (hpr ▸ r.2).symm
    change 0 = (LinearMap.ker (lambdaBlock m (degB2 q))).starProjection
      (blockProj degB2 (lp.single 2 p (F p)) (degB2 q)) ⟨q, rfl⟩
    rw [hz, map_zero]
    rfl

end GaussianTesting
