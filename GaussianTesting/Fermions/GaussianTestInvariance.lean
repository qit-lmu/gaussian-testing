module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.GaussianOrbits

@[expose] public section

/-!
# Gaussian invariance of the fermionic test

Equation (5.2): orthogonality of the Majorana rotation implies that its
implementer, applied to both copies, commutes with `Λ`.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable {m : ℕ}

/-- The action of a fermionic unitary on two copies. -/
def fermionPairAction (U : HF m ≃ₗᵢ[ℂ] HF m) : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) :=
  opL U.toLinearEquiv.toLinearMap ∘ₗ opR U.toLinearEquiv.toLinearMap

@[simp] theorem fermionPairAction_tp2 (U : HF m ≃ₗᵢ[ℂ] HF m) (ψ φ : HF m) :
    fermionPairAction U (tp2 ψ φ) = tp2 (U ψ) (U φ) := by
  simp [fermionPairAction, opL_tp2, opR_tp2]

theorem lambdaF_tp2 (ψ φ : HF m) :
    lambdaF m (tp2 ψ φ) = ∑ a, tp2 (maj a ψ) (maj a φ) := by
  simp [lambdaF, opL_tp2, opR_tp2]

private theorem rotation_rows (R : FermionRotation m) (b c : Fin m × Bool) :
    ∑ a, (R.val b a : ℂ) * (R.val c a : ℂ) =
      if b = c then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ => A b c)
    ((Matrix.mem_orthogonalGroup_iff _ _).mp R.property.1)
  have h' : ∑ a, R.val b a * R.val c a =
      if b = c then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero] using congrArg Complex.ofReal h'

/-- The orthogonality calculation in Eq. (5.2), on elementary tensors. -/
theorem ImplementsMajoranaRotation.lambdaF_tp2 {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U) (ψ φ : HF m) :
    fermionPairAction U (lambdaF m (tp2 ψ φ)) =
      lambdaF m (tp2 (U ψ) (U φ)) := by
  classical
  have hc (a : Fin m × Bool) (v : HF m) :
      U (maj a v) = ∑ b, (R.val b a : ℂ) • maj b (U v) := by
    simpa using hU.majorana a (U v)
  rw [GaussianTesting.lambdaF_tp2, map_sum, GaussianTesting.lambdaF_tp2]
  simp only [fermionPairAction_tp2, hc]
  ext p
  simp only [WithLp.ofLp_sum, Finset.sum_apply, tp2_apply, PiLp.smul_apply,
    smul_eq_mul, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl fun b _ => Finset.sum_comm)
  have ht (b c : Fin m × Bool) :
      ∑ a, (R.val b a * maj b (U ψ) p.1) *
        (R.val c a * maj c (U φ) p.2) =
      (if b = c then 1 else 0 : ℂ) * (maj b (U ψ) p.1 * maj c (U φ) p.2) := by
    rw [← rotation_rows R b c, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp only [ht]
  simp

/-- Equation (5.2), as commutation on the full two-copy Hilbert space. -/
theorem ImplementsMajoranaRotation.lambdaF_comm {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (f : H2 (Qm m)) :
    fermionPairAction U (lambdaF m f) = lambdaF m (fermionPairAction U f) := by
  classical
  have hf : f = ∑ i : Qm m, ∑ j : Qm m, f (i, j) •
      tp2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    ext p
    simp [WithLp.ofLp_sum, Finset.sum_apply, tp2_apply, EuclideanSpace.single,
      PiLp.single_apply, smul_eq_mul]
  rw [hf]
  simp only [map_sum, map_smul, fermionPairAction_tp2, hU.lambdaF_tp2]

private theorem pair_basis_expansion (f : H2 (Qm m)) :
    f = ∑ i : Qm m, ∑ j : Qm m, f (i, j) •
      tp2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  classical
  ext p
  simp [WithLp.ofLp_sum, Finset.sum_apply, tp2_apply, EuclideanSpace.single,
    PiLp.single_apply, smul_eq_mul]

theorem fermionPairAction_symm_apply (U : HF m ≃ₗᵢ[ℂ] HF m) (f : H2 (Qm m)) :
    fermionPairAction U (fermionPairAction U.symm f) = f := by
  classical
  rw [pair_basis_expansion f]
  simp only [map_sum, map_smul, fermionPairAction_tp2, U.apply_symm_apply]

theorem fermionPairAction_inner (U : HF m ≃ₗᵢ[ℂ] HF m) (f g : H2 (Qm m)) :
    ⟪fermionPairAction U f, fermionPairAction U g⟫_ℂ = ⟪f, g⟫_ℂ := by
  classical
  rw [pair_basis_expansion f, pair_basis_expansion g]
  simp only [map_sum, map_smul, fermionPairAction_tp2, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, inner_tp2_tp2, U.inner_map_map]

/-- Equation (5.2), including conjugation by the inverse on both copies. -/
theorem ImplementsMajoranaRotation.lambdaF_conjugate {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (f : H2 (Qm m)) :
    fermionPairAction U (lambdaF m (fermionPairAction U.symm f)) = lambdaF m f := by
  rw [hU.lambdaF_comm, fermionPairAction_symm_apply]

/-- The kernel projection commutes with the two-copy Gaussian action. -/
theorem ImplementsMajoranaRotation.PF_comm {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U)
    (f : H2 (Qm m)) :
    PF m (fermionPairAction U f) = fermionPairAction U (PF m f) := by
  change (LinearMap.ker (lambdaF m)).starProjection (fermionPairAction U f) = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change lambdaF m (fermionPairAction U (PF m f)) = 0
    rw [← hU.lambdaF_comm]
    have hmem := (LinearMap.ker (lambdaF m)).starProjection_apply_mem f
    change lambdaF m (PF m f) = 0 at hmem
    rw [hmem, map_zero]
  · intro w hw
    have hinv : fermionPairAction U.symm w ∈ LinearMap.ker (lambdaF m) := by
      change lambdaF m (fermionPairAction U.symm w) = 0
      rw [← LinearIsometryEquiv.inv_def, ← hU.inv.lambdaF_comm]
      change lambdaF m w = 0 at hw
      rw [hw, map_zero]
    rw [← map_sub]
    conv_lhs => rhs; rw [← fermionPairAction_symm_apply U w]
    rw [fermionPairAction_inner]
    exact (LinearMap.ker (lambdaF m)).starProjection_inner_eq_zero f _ hinv

/-- The manuscript's acceptance probability is invariant under Gaussian unitaries. -/
theorem ImplementsMajoranaRotation.accProb_PF {R : FermionRotation m}
    {U : HF m ≃ₗᵢ[ℂ] HF m} (hU : ImplementsMajoranaRotation R U) (ψ : HF m) :
    accProb (PF m) (U ψ) = accProb (PF m) ψ := by
  unfold accProb
  rw [← fermionPairAction_tp2, hU.PF_comm, fermionPairAction_inner]

/-- The forward implication of Lemma 5.1 from the independent Gaussian orbits. -/
theorem fermionicGaussian_lambdaF_eq_zero {ψ : HF m}
    (hψ : ψ ∈ fermionicGaussianStates m) : lambdaF m (tp2 ψ ψ) = 0 := by
  rcases hψ with ⟨x, _, U, hU, rfl⟩ | ⟨x, _, U, hU, rfl⟩ <;>
    obtain ⟨R, hR⟩ := hU <;>
    rw [← hR.lambdaF_tp2, lambdaF_tp2_single, map_zero]

end
end GaussianTesting
