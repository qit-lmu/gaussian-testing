module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberCoreDense
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Rotation invariants and the closed Schrödinger generator

Averaging the actual periodic rotation group preserves polynomial Gaussians:
each polynomial orbit lies in a finite-dimensional polynomial Gaussian span.
The averaged vectors have zero generator. Density and the closed graph then
identify the rotation-fixed subspace with the kernel of the manuscript's
closed operator `Λ`.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

attribute [local irreducible] schrodingerRotation

/-- The wavefunction rotation has period `2π`. -/
theorem schrodingerRotation_periodic (m : ℕ) (f : SchrodingerSpace m) :
    Function.Periodic (fun θ => schrodingerRotation m θ f) (2 * Real.pi) := by
  intro θ
  have hr (z : BosonConfig m) : bosonRotate (θ + 2 * Real.pi) z = bosonRotate θ z := by
    ext ij
    simp only [bosonRotate, Real.cos_add_two_pi, Real.sin_add_two_pi]
  apply Lp.ext
  filter_upwards [schrodingerRotation_coeFn m (θ + 2 * Real.pi) f,
    schrodingerRotation_coeFn m θ f] with z h₁ h₂
  rw [h₁, h₂, hr]

/-- The normalized average over one full period of the actual rotation group. -/
def schrodingerRotationAverage (m : ℕ) (f : SchrodingerSpace m) : SchrodingerSpace m :=
  (2 * Real.pi)⁻¹ • ∫ θ in 0..2 * Real.pi, schrodingerRotation m θ f

/-- Strong continuity of the group makes its period average continuous. -/
theorem continuous_schrodingerRotationAverage (m : ℕ) :
    Continuous (schrodingerRotationAverage m) := by
  have h : Continuous (fun p : SchrodingerSpace m × ℝ => schrodingerRotation m p.2 p.1) :=
    (continuous_schrodingerRotation_apply m).comp
      (show Continuous (Prod.swap : SchrodingerSpace m × ℝ → ℝ × SchrodingerSpace m)
        from continuous_swap)
  have hi : Continuous (fun f : SchrodingerSpace m =>
      ∫ θ in 0..2 * Real.pi, schrodingerRotation m θ f) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun f θ => schrodingerRotation m θ f) h 0 (2 * Real.pi)
  exact hi.const_smul ((2 * Real.pi)⁻¹)

/-- Averaging over a complete period produces a rotation-invariant vector. -/
theorem schrodingerRotationAverage_fixed (m : ℕ) (f : SchrodingerSpace m) (θ : ℝ) :
    schrodingerRotation m θ (schrodingerRotationAverage m f) =
      schrodingerRotationAverage m f := by
  unfold schrodingerRotationAverage
  rw [LinearMapClass.map_smul_of_tower]
  congr 1
  change (schrodingerRotation m θ).toLinearIsometry
    (∫ t in 0..2 * Real.pi, schrodingerRotation m t f) = _
  rw [← (schrodingerRotation m θ).toLinearIsometry.intervalIntegral_comp_comm]
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, ← schrodingerRotation_add]
  rw [intervalIntegral.integral_comp_add_left (fun t => schrodingerRotation m t f) θ]
  simpa only [add_zero, zero_add] using
    (schrodingerRotation_periodic m f).intervalIntegral_add_eq θ 0

/-- The average acts as the identity on fixed vectors. -/
theorem schrodingerRotationAverage_eq_self (m : ℕ) (f : SchrodingerSpace m)
    (hf : ∀ θ, schrodingerRotation m θ f = f) : schrodingerRotationAverage m f = f := by
  unfold schrodingerRotationAverage
  simp only [hf, intervalIntegral.integral_const, sub_zero, smul_smul]
  rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_smul]

/-- A polynomial Gaussian remains a polynomial Gaussian after period averaging. -/
theorem schrodingerRotationAverage_polynomialGaussian (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    ∃ q : MvPolynomial (Fin 2 × Fin m) ℂ,
      polynomialGaussian q = schrodingerRotationAverage m (polynomialGaussian p) := by
  obtain ⟨κ, hκ, c, c', v, _, hv, _⟩ := polynomialRotate_hasFiniteCurveDeriv m p
  let : Fintype κ := hκ
  let M : Submodule ℂ (SchrodingerSpace m) :=
    Submodule.span ℂ (Set.range (fun i => polynomialGaussian (v i)))
  have : FiniteDimensional ℂ M :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have horbit (t : ℝ) : schrodingerRotation m t (polynomialGaussian p) ∈ M := by
    rw [← polynomialGaussian_rotate, show polynomialRotate m t p = ∑ i, c i t • v i from hv t]
    change polynomialGaussianLinear (∑ i, c i t • v i) ∈ M
    rw [_root_.map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hInt : (∫ t in 0..2 * Real.pi,
      schrodingerRotation m t (polynomialGaussian p)) ∈ M := by
    apply M.starProjection_eq_self_iff.mp
    rw [← M.starProjection.intervalIntegral_comp_comm
      ((continuous_schrodingerRotation m (polynomialGaussian p)).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    exact M.starProjection_eq_self_iff.mpr (horbit t)
  have havg : schrodingerRotationAverage m (polynomialGaussian p) ∈ M := by
    unfold schrodingerRotationAverage
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact M.smul_mem _ hInt
  have hM : M ≤ LinearMap.range (polynomialGaussianLinear (ι := Fin 2 × Fin m)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, rfl⟩
  exact hM havg

/-- On polynomial Gaussians, being fixed by every rotation forces the displayed
creation-annihilation generator to vanish. -/
theorem polynomialLambda_eq_zero_of_rotation_fixed (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ)
    (hp : ∀ θ, schrodingerRotation m θ (polynomialGaussian p) = polynomialGaussian p) :
    polynomialGaussian (polynomialLambda m p) = 0 := by
  have hderiv := hasDerivAt_schrodingerRotation_polynomialGaussian_zero m p
  have hconst : HasDerivAt (fun θ : ℝ => schrodingerRotation m θ (polynomialGaussian p))
      0 0 := by
    simpa only [hp] using hasDerivAt_const (0 : ℝ) (polynomialGaussian p)
  have hz : (-Complex.I) • polynomialGaussian (polynomialLambda m p) = 0 :=
    hderiv.unique hconst
  exact (smul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

/-- Averaging a polynomial Gaussian lies in the kernel of the prescribed
finite-core closure. -/
theorem schrodingerRotationAverage_polynomialGaussian_mem_kernel (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    schrodingerRotationAverage m (polynomialGaussian p) ∈ (schrodingerLambda m).ker := by
  obtain ⟨q, hq⟩ := schrodingerRotationAverage_polynomialGaussian m p
  have hqfix (θ : ℝ) : schrodingerRotation m θ (polynomialGaussian q) =
      polynomialGaussian q := by
    rw [hq]
    exact schrodingerRotationAverage_fixed m (polynomialGaussian p) θ
  have hzero := polynomialLambda_eq_zero_of_rotation_fixed m q hqfix
  have hcore : q ∈ finiteFockPolynomialCore m := by
    rw [finiteFockPolynomialCore_eq_top]
    exact Submodule.mem_top
  have hg : (polynomialGaussian q, 0) ∈ (schrodingerLambda m).graph := by
    rw [schrodingerLambda_graph]
    apply (schrodingerFiniteFockGraph m).le_topologicalClosure
    rw [← hzero]
    exact ⟨⟨q, hcore⟩, rfl⟩
  obtain ⟨x, hx, hy⟩ := (schrodingerLambda m).mem_graph_iff.mp hg
  rw [← hq]
  exact (schrodingerLambda m).mem_ker_iff.mpr ⟨x, hx.symm, hy⟩

/-- The period average of every `L²` vector is in the actual closed kernel. -/
theorem schrodingerRotationAverage_mem_kernel (m : ℕ) (f : SchrodingerSpace m) :
    schrodingerRotationAverage m f ∈ (schrodingerLambda m).ker := by
  exact isClosed_property denseRange_polynomialGaussian
    ((schrodingerLambda_kernel_isClosed m).preimage (continuous_schrodingerRotationAverage m))
    (schrodingerRotationAverage_polynomialGaussian_mem_kernel m) f

/-- Every vector fixed by all physical rotations belongs to the kernel of the
manuscript's graph-closed generator. -/
theorem schrodingerLambda_mem_kernel_of_rotation_fixed (m : ℕ)
    {f : SchrodingerSpace m} (hf : ∀ θ, schrodingerRotation m θ f = f) :
    f ∈ (schrodingerLambda m).ker := by
  simpa only [schrodingerRotationAverage_eq_self m f hf] using
    schrodingerRotationAverage_mem_kernel m f

/-- The closed generator kernel is exactly the invariant subspace of the
actual strongly continuous rotation group. -/
theorem schrodingerLambda_mem_kernel_iff_rotation_fixed (m : ℕ) (f : SchrodingerSpace m) :
    f ∈ (schrodingerLambda m).ker ↔ ∀ θ, schrodingerRotation m θ f = f :=
  ⟨fun hf => schrodingerRotation_fixed_of_mem_kernel m hf,
    schrodingerLambda_mem_kernel_of_rotation_fixed m⟩

end
end GaussianTesting
