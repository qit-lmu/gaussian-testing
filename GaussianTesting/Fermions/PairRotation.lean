module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.PairRepresentation
public import GaussianTesting.Fermions.CopyRotationDerivative
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# The two-copy rotation-fixed subspace

The second-quantized SO(2) action has standard-angle derivative `i L/2`.
Consequently its invariant subspace is exactly `ker Λ`, as asserted after
Eq. (5.5) of the manuscript.
-/

namespace GaussianTesting

noncomputable section

open Matrix

/-- The usual oriented rotation of the two copy coordinates. -/
def fermionPairCircle (θ : ℝ) : FermionModeRotation 2 :=
  ⟨planeRotationMatrix 0 1 (Real.cos θ) (-Real.sin θ),
    planeRotationMatrix_mem (by decide) (by nlinarith [Real.sin_sq_add_cos_sq θ])⟩

@[simp] theorem fermionPairCircle_val (θ : ℝ) :
    (fermionPairCircle θ).val = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fermionPairCircle, planeRotationMatrix]

@[simp] theorem fermionPairCircle_zero : fermionPairCircle 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem fermionPairCircle_add (s t : ℝ) :
    fermionPairCircle (s + t) = fermionPairCircle s * fermionPairCircle t := by
  apply Subtype.ext
  change (fermionPairCircle (s + t)).val = (fermionPairCircle s).val * (fermionPairCircle t).val
  simp only [fermionPairCircle_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem continuous_fermionPairCircle : Continuous fermionPairCircle := by
  apply Continuous.subtype_mk
  change Continuous (fun θ => planeRotationMatrix (0 : Fin 2) 1 (Real.cos θ) (-Real.sin θ))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · simpa [planeRotationMatrix] using Real.continuous_cos
  · change Continuous (fun θ : ℝ => -Real.sin θ)
    fun_prop
  · simpa [planeRotationMatrix] using Real.continuous_sin
  · simpa [planeRotationMatrix] using Real.continuous_cos

private theorem coordinatePlaneRotation_eq_pairCircle (a b : Fin 2) (p q : ℝ)
    (hab : a ≠ b) (hpq : p ^ 2 + q ^ 2 = 1) :
    ∃ θ, coordinatePlaneRotation a b p q hab hpq = fermionPairCircle θ := by
  let z : ℂ := ⟨p, q⟩
  have hz : ‖z‖ = 1 := by
    simp only [z, Complex.norm_def, Complex.normSq_mk, ← pow_two, hpq, Real.sqrt_one]
  have hc : Real.cos z.arg = p := by simpa only [hz, one_mul] using Complex.norm_mul_cos_arg z
  have hs : Real.sin z.arg = q := by simpa only [hz, one_mul] using Complex.norm_mul_sin_arg z
  fin_cases a <;> fin_cases b <;> try exact (hab rfl).elim
  · refine ⟨-z.arg, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, fermionPairCircle, planeRotationMatrix, hc, hs]
  · refine ⟨z.arg, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinatePlaneRotation, fermionPairCircle, planeRotationMatrix, hc, hs]

variable {m : ℕ}

/-- The actual second-quantized pair action has generator `i L/2`. -/
theorem fermionPairRepresentation_hasDerivAt (v : H2 (Qm m)) :
    HasDerivAt (fun θ => fermionPairRepresentation m (fermionPairCircle θ) v)
      (fermionPairGenerator m v) 0 := by
  have hcomm (A : Module.End ℂ (H2 (Qm m)))
      (hA : ∀ r a, A * fermionPairMajorana r a = fermionPairMajorana r a * A) :
      ∃ z : ℂ, A = z • LinearMap.id := by
    apply exists_scalar_of_commutes_fermionPairMajorana
    intro r a v
    exact congrArg (fun T : Module.End ℂ (H2 (Qm m)) => T v) (hA r a)
  have hzero : (fermionPairCircle 0).val = 1 := by rw [fermionPairCircle_zero]; rfl
  have hK (r s : Fin 2) : HasDerivAt (fun t => (fermionPairCircle t).val r s)
      (!![0, -1; 1, 0] r s) 0 := by
    simp only [fermionPairCircle_val]
    fin_cases r <;> fin_cases s
    all_goals first
      | simpa using Real.hasDerivAt_cos 0
      | simpa using Real.hasDerivAt_sin 0
      | simpa using (Real.hasDerivAt_sin 0).const_mul (-1)
  apply unitary_oneParameter_deriv_of_majorana_covariance
    (fun θ => fermionPairRepresentation m (fermionPairCircle θ))
    (fun v => (continuous_fermionPairRepresentation_orbit v).comp continuous_fermionPairCircle)
    (by simp) (by intro s t; rw [fermionPairCircle_add, map_mul])
    fermionPairMajorana hcomm (fermionPairVacuum m) (fermionPairVacuum_ne_zero m)
    (fun θ => fermionPairRepresentation_vacuum (fermionPairCircle θ))
    (fun θ => (fermionPairCircle θ).val) !![0, -1; 1, 0] hzero hK
    (fun θ r a v => fermionPairRepresentation_majorana (fermionPairCircle θ) r a v)
    (fermionPairGenerator m) fermionPairGenerator_vacuum _ v
  intro r a
  have h := fermionPairGenerator_comm r a
  fin_cases r <;> simpa [Fin.sum_univ_two] using h

/-- Fixing every two-copy angle is equivalent to the manuscript kernel condition. -/
theorem fermionPairCircle_fixed_iff (v : H2 (Qm m)) :
    (∀ θ, fermionPairRepresentation m (fermionPairCircle θ) v = v) ↔ lambdaF m v = 0 := by
  have h := unitary_oneParameter_fixed_iff_of_deriv_zero
    (fun θ => fermionPairRepresentation m (fermionPairCircle θ))
    (fun v => (continuous_fermionPairRepresentation_orbit v).comp continuous_fermionPairCircle)
    (by simp) (by intro s t; rw [fermionPairCircle_add, map_mul])
    (fermionPairGenerator m) fermionPairRepresentation_hasDerivAt v
  rw [← LinearMap.mem_ker, ker_fermionPairGenerator, LinearMap.mem_ker] at h
  exact h

/-- The full second-quantized SO(2)-invariant subspace is `ker Λ`. -/
theorem fermionPairRepresentation_fixed_iff (v : H2 (Qm m)) :
    (∀ R, fermionPairRepresentation m R v = v) ↔ lambdaF m v = 0 := by
  rw [← fermionPairCircle_fixed_iff]
  constructor
  · intro h θ
    exact h _
  · intro h R
    induction R using specialOrthogonal_induction with
    | h1 => simp
    | hmul A B hA hB =>
      rw [map_mul]
      change fermionPairRepresentation m A (fermionPairRepresentation m B v) = v
      rw [hB, hA]
    | hinv A hA =>
      have he : fermionPairRepresentation m A⁻¹ (fermionPairRepresentation m A v) = v := by
        change (fermionPairRepresentation m A⁻¹ * fermionPairRepresentation m A) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      rwa [hA] at he
    | hplane a b p q hab hpq =>
      obtain ⟨θ, he⟩ := coordinatePlaneRotation_eq_pairCircle a b p q hab hpq
      rw [he]
      exact h θ

/-- The accepting space is the fixed subspace of the actual pair representation. -/
theorem fermionPairRepresentation_fixedSubspace :
    UnitaryRepresentation.fixedSubspace (fermionPairRepresentation m) ⊤ =
      LinearMap.ker (lambdaF m) := by
  ext v
  change (∀ R, R ∈ (⊤ : Subgroup (FermionModeRotation 2)) →
    fermionPairRepresentation m R v = v) ↔ lambdaF m v = 0
  simp only [Subgroup.mem_top, forall_true_left]
  exact fermionPairRepresentation_fixed_iff v

/-- The manuscript's `P` is exactly the projection onto SO(2)-invariant vectors. -/
theorem PF_eq_pairRotation_fixedProjection :
    PF m = (UnitaryRepresentation.fixedSubspace (fermionPairRepresentation m) ⊤).starProjection.toLinearMap := by
  simp only [fermionPairRepresentation_fixedSubspace]
  rfl

end
end GaussianTesting
