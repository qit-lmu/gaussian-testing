module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.BellEigenvalues

@[expose] public section

/-!
# Figure 1(a): fermionic Bell-measurement readout

The Bell decoder followed by the classical zero-eigenvalue rule has accepting
projection `PF`. The identity holds on the full two-copy Hilbert space.
-/

namespace GaussianTesting

noncomputable section

attribute [local instance] Classical.propDecidable

def bellOutcomeMask {ι : Type*} [Fintype ι] (accepts : ι → Prop) :
    H ι →ₗ[ℂ] H ι := by
  classical
  exact
    { toFun := fun f => WithLp.toLp 2 fun z => if accepts z then f z else 0
      map_add' := by intro f g; ext z; by_cases hz : accepts z <;> simp [hz]
      map_smul' := by intro c f; ext z; by_cases hz : accepts z <;> simp [hz] }

private theorem bellOutcomeMask_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (accepts : ι → Prop) (z : ι) :
    bellOutcomeMask accepts (EuclideanSpace.single z 1) =
      if accepts z then EuclideanSpace.single z 1 else 0 := by
  classical
  ext w
  by_cases hz : accepts z
  · by_cases hw : w = z
    · subst w; simp [bellOutcomeMask, hz]
    · simp [bellOutcomeMask, EuclideanSpace.single, PiLp.single_apply, hz, hw]
  · by_cases hw : w = z
    · subst w; simp [bellOutcomeMask, hz]
    · simp [bellOutcomeMask, EuclideanSpace.single, PiLp.single_apply, hz, hw]

private theorem bellOutcomeMask_inner {ι : Type*} [Fintype ι]
    (accepts : ι → Prop) (f : H ι) :
    (inner ℂ f (bellOutcomeMask accepts f)).re =
      ∑ z, if accepts z then ‖f z‖ ^ 2 else 0 := by
  classical
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (inner ℂ (f z) (if accepts z then f z else 0)).re = _
  by_cases hz : accepts z
  · simp only [ite_eq_left hz, inner_self_eq_norm_sq_to_K]
    norm_cast
  · simp [hz]

private theorem PF_eigen {m : ℕ} (f : H2 (Qm m)) (c : ℂ)
    (hf : lambdaF m f = c • f) :
    PF m f = if c = 0 then f else 0 := by
  classical
  change (LinearMap.ker (lambdaF m)).starProjection f = _
  split_ifs with hc
  · apply (LinearMap.ker (lambdaF m)).starProjection_eq_self_iff.mpr
    rw [LinearMap.mem_ker, hf, hc, zero_smul]
  · apply (LinearMap.ker (lambdaF m)).eq_starProjection_of_mem_of_inner_eq_zero
      (Submodule.zero_mem _)
    intro w hw
    have h := lambdaF_isSymmetric f w
    rw [hf, LinearMap.mem_ker.mp hw, inner_zero_right, inner_smul_left] at h
    simp only [sub_zero]
    exact (mul_eq_zero.mp h).resolve_left (by simpa using hc)

/-- The diagonal projection onto the accepted classical Bell outcomes.
The integer score is computed directly from the two output bitstrings. -/
def fermionicBellOutcomeProjection (m : ℕ) : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) :=
  bellOutcomeMask (fermionicBellAccepts m)

@[simp] theorem fermionicBellOutcomeProjection_apply (m : ℕ) (f : H2 (Qm m))
    (z : Qm m × Qm m) :
    fermionicBellOutcomeProjection m f z = if fermionicBellAccepts m z then f z else 0 :=
  rfl

/-- The accepting observable of Figure 1(a): apply the Bell decoder,
measure both bitstrings, and accept precisely the zero-score outcomes.
The inverse of this unitary is its adjoint, so this is `U_Bell† D_A U_Bell`. -/
def fermionicBellMeasurement (m : ℕ) : H2 (Qm m) →ₗ[ℂ] H2 (Qm m) :=
  (fermionicBellReadout m).symm.toLinearMap ∘ₗ fermionicBellOutcomeProjection m ∘ₗ
    (fermionicBellReadout m).toLinearMap

private theorem fermionicBellMeasurement_basis (m : ℕ) (z : Qm m × Qm m) :
    fermionicBellMeasurement m (fermionicBellBasis m z) =
      if fermionicBellAccepts m z then fermionicBellBasis m z else 0 := by
  change (fermionicBellReadout m).symm (bellOutcomeMask (fermionicBellAccepts m)
    (fermionicBellReadout m (fermionicBellBasis m z))) = _
  rw [fermionicBellReadout_basis, bellOutcomeMask_single]
  split_ifs <;> simp [fermionicBellReadout, OrthonormalBasis.repr_symm_single]

private theorem PF_fermionicBellBasis (m : ℕ) (z : Qm m × Qm m) :
    PF m (fermionicBellBasis m z) =
      if fermionicBellAccepts m z then fermionicBellBasis m z else 0 := by
  have h := PF_eigen (fermionicBellBasis m z) (fermionicBellEigenvalue m z : ℂ)
    (lambdaF_fermionicBellBasis z)
  by_cases hz : fermionicBellEigenvalue m z = 0
  · simpa [fermionicBellAccepts, hz] using h
  · have hc : (fermionicBellEigenvalue m z : ℂ) ≠ 0 := by exact_mod_cast hz
    simpa [fermionicBellAccepts, hz, hc] using h

/-- **Figure 1(a).** The accepting Bell-readout projection is exactly the
orthogonal projection onto `ker Λ`, on the whole two-copy Hilbert space. -/
theorem fermionicBellMeasurement_eq_PF (m : ℕ) :
    fermionicBellMeasurement m = PF m := by
  apply (fermionicBellBasis m).toBasis.ext
  intro z
  change fermionicBellMeasurement m (fermionicBellBasis m z) = PF m (fermionicBellBasis m z)
  rw [fermionicBellMeasurement_basis, PF_fermionicBellBasis]

/-- Summing Born probabilities over exactly the accepted Bell bitstrings
gives the expectation of `PF`, for an arbitrary two-copy input vector. -/
theorem fermionicBellReadout_probability {m : ℕ} (f : H2 (Qm m)) :
    (∑ z, if fermionicBellAccepts m z then ‖fermionicBellReadout m f z‖ ^ 2 else 0) =
      (inner ℂ f (PF m f)).re := by
  have h := (fermionicBellReadout m).inner_map_map f (fermionicBellMeasurement m f)
  have hu : fermionicBellReadout m (fermionicBellMeasurement m f) =
      bellOutcomeMask (fermionicBellAccepts m) (fermionicBellReadout m f) :=
    (fermionicBellReadout m).apply_symm_apply _
  rw [hu, fermionicBellMeasurement_eq_PF] at h
  exact (bellOutcomeMask_inner (fermionicBellAccepts m) (fermionicBellReadout m f)).symm.trans
    (congrArg Complex.re h)

/-- **Figure 1(a).** On two identical input copies, the circuit has exactly
the manuscript's acceptance probability `p(ψ)`. -/
theorem fermionicBellMeasurement_acceptance {m : ℕ} (ψ : HF m) :
    (inner ℂ (tp2 ψ ψ) (fermionicBellMeasurement m (tp2 ψ ψ))).re =
      accProb (PF m) ψ := by
  rw [fermionicBellMeasurement_eq_PF]
  rfl

end
end GaussianTesting
