module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Generators of the finite-dimensional axis actions

The continuous axis actions in a finite-dimensional unitary representation
are norm-continuous one-parameter groups. Averaging over a small interval
provides an invertible smoothing operator and proves differentiability,
without assuming a differentiable representation. This supplies the axis
generator step in the group-to-Lie-algebra passage for Theorem 4.1.
-/

namespace GaussianTesting

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 600000

private theorem oneParameter_integral_translate
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (U : ℝ → A) (hU : Continuous U) (hmul : ∀ s t, U (s + t) = U s * U t)
    (s t : ℝ) :
    U s * (∫ r in (0 : ℝ)..t, U r) =
      (∫ r in (0 : ℝ)..(s + t), U r) - ∫ r in (0 : ℝ)..s, U r := by
  rw [intervalIntegral.integral_interval_sub_left (hU.intervalIntegrable _ _)
    (hU.intervalIntegrable _ _)]
  calc
    U s * (∫ r in (0 : ℝ)..t, U r) = ∫ r in (0 : ℝ)..t, U s * U r :=
      ((ContinuousLinearMap.mul ℝ A (U s)).intervalIntegral_comp_comm
        (hU.intervalIntegrable 0 t)).symm
    _ = ∫ r in (0 : ℝ)..t, U (s + r) := by simp_rw [hmul]
    _ = _ := by simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := t) U s

/-- A norm-continuous one-parameter group in a real Banach algebra has a
bounded infinitesimal generator. No differentiability assumption is needed. -/
theorem continuous_oneParameter_exists_generator
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (U : ℝ → A) (hU : Continuous U) (hzero : U 0 = 1)
    (hmul : ∀ s t, U (s + t) = U s * U t) :
    ∃ D : A, ∀ t : ℝ, HasDerivAt U (U t * D) t := by
  let F : ℝ → A := fun t => ∫ r in (0 : ℝ)..t, U r
  have hF (t : ℝ) : HasDerivAt F (U t) t :=
    (hU.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • F t) (𝓝[≠] 0) (𝓝 (1 : A)) := by
    simpa only [zero_add, F, intervalIntegral.integral_same,
      sub_zero, hzero] using (hF 0).tendsto_slope_zero
  have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℝ), IsUnit (t⁻¹ • F t) :=
    hlim.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨t, ht⟩ := hevent.exists
  obtain ⟨b, hb⟩ := ht
  let D : A := (t⁻¹ • (U t - 1)) * (↑b⁻¹ : A)
  refine ⟨D, fun s => ?_⟩
  have hidentity : U = fun s => (t⁻¹ • (F (s + t) - F s)) * (↑b⁻¹ : A) := by
    funext s
    have ht' : U s * (b : A) = t⁻¹ • (F (s + t) - F s) := by
      rw [hb, mul_smul_comm, oneParameter_integral_translate U hU hmul]
    rw [← ht', mul_assoc]
    simp
  have hd : HasDerivAt (fun r => (t⁻¹ • (F (r + t) - F r)) * (↑b⁻¹ : A))
      ((t⁻¹ • (U (s + t) - U s)) * (↑b⁻¹ : A)) s := by
    convert ((((hF (s + t)).scomp s ((hasDerivAt_id s).add_const t)).sub
      (hF s)).const_smul t⁻¹).mul_const (↑b⁻¹ : A) using 1 <;> simp
  rw [← hidentity] at hd
  convert hd using 1
  dsimp [D]
  rw [hmul, ← mul_assoc, mul_smul_comm, mul_sub, mul_one]

/-- Differentiating conjugation by a one-parameter group produces the
commutator with its generator. -/
theorem oneParameter_conjugation_hasDerivAt
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {U : ℝ → A} {D : A} (hzero : U 0 = 1)
    (hD : ∀ t, HasDerivAt U (U t * D) t) (B : A) :
    HasDerivAt (fun s => U s * B * U (-s)) (D * B - B * D) 0 := by
  have h0 : HasDerivAt U D 0 := by simpa only [hzero, one_mul] using hD 0
  have hn : HasDerivAt (fun s => U (-s)) (-D) 0 := by
    convert (hD (-(0 : ℝ))).scomp (0 : ℝ) (hasDerivAt_id (0 : ℝ)).neg using 1 <;>
      simp [hzero, Function.comp_def]
  convert (h0.mul_const B).mul hn using 1; simp [hzero, sub_eq_add_neg]

/-- The usual rotation law for two axis generators implies their Lie
commutator relation by differentiation at zero. -/
theorem oneParameter_rotationLaw_commutator
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {U : ℝ → A} {D B C : A} (hzero : U 0 = 1)
    (hD : ∀ t, HasDerivAt U (U t * D) t)
    (hconj : ∀ s, U s * B * U (-s) = Real.cos s • B + Real.sin s • C) :
    D * B - B * D = C := by
  have hd := oneParameter_conjugation_hasDerivAt hzero hD B
  have hr : HasDerivAt (fun s => Real.cos s • B + Real.sin s • C) C 0 := by
    convert ((Real.hasDerivAt_cos 0).smul_const B).add
      ((Real.hasDerivAt_sin 0).smul_const C) using 1; simp
  exact hd.unique (hr.congr_of_eventuallyEq (Filter.Eventually.of_forall hconj))

/-- The derivative of an axis-coordinate product at the identity is the
corresponding linear combination of its three infinitesimal generators. -/
theorem oneParameter_triple_hasDerivAt
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {Ux Uy Uz : ℝ → A} {Dx Dy Dz : A}
    (hx0 : Ux 0 = 1) (hy0 : Uy 0 = 1) (hz0 : Uz 0 = 1)
    (hx : HasDerivAt Ux Dx 0) (hy : HasDerivAt Uy Dy 0) (hz : HasDerivAt Uz Dz 0)
    {a b c : ℝ → ℝ} {a' b' c' : ℝ}
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0)
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) (hc : HasDerivAt c c' 0) :
    HasDerivAt (fun t => Ux (a t) * Uy (b t) * Uz (c t))
      (a' • Dx + b' • Dy + c' • Dz) 0 := by
  have hxa : HasDerivAt (fun t => Ux (a t)) (a' • Dx) 0 := by
    exact (ha0 ▸ hx).scomp 0 ha
  have hyb : HasDerivAt (fun t => Uy (b t)) (b' • Dy) 0 := by
    exact (hb0 ▸ hy).scomp 0 hb
  have hzc : HasDerivAt (fun t => Uz (c t)) (c' • Dz) 0 := by
    exact (hc0 ▸ hz).scomp 0 hc
  convert (hxa.mul hyb).mul hzc using 1; simp [ha0, hb0, hc0, hx0, hy0, hz0]

/-- A local Euler factorization of a conjugated axis path determines the
conjugated infinitesimal generator. This is the calculus step used to pass
from explicit SO(3) matrices to their represented Lie algebra. -/
theorem oneParameter_conjugation_generator_of_local_factorization
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {Ux Uy Uz : ℝ → A} {Dx Dy Dz : A}
    (hx0 : Ux 0 = 1) (hy0 : Uy 0 = 1) (hz0 : Uz 0 = 1)
    (hx : HasDerivAt Ux Dx 0) (hy : HasDerivAt Uy Dy 0) (hz : HasDerivAt Uz Dz 0)
    (s : ℝ) {a b c : ℝ → ℝ} {a' b' c' : ℝ}
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = 0)
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) (hc : HasDerivAt c c' 0)
    (hfactor : ∀ᶠ t in 𝓝 (0 : ℝ),
      Ux s * Uy t * Ux (-s) = Ux (a t) * Uy (b t) * Uz (c t)) :
    Ux s * Dy * Ux (-s) = a' • Dx + b' • Dy + c' • Dz := by
  have hleft := (hy.const_mul (Ux s)).mul_const (Ux (-s))
  have hright := oneParameter_triple_hasDerivAt hx0 hy0 hz0 hx hy hz
    ha0 hb0 hc0 ha hb hc
  exact hleft.unique (hright.congr_of_eventuallyEq hfactor)

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Evaluating a differentiable operator-valued curve gives its vector derivative. -/
theorem oneParameter_generator_hasDerivAt_apply
    {U : ℝ → E →L[ℂ] E} {D : E →L[ℂ] E}
    (hD : ∀ t, HasDerivAt U (U t * D) t) (t : ℝ) (v : E) :
    HasDerivAt (fun s => U s v) (U t (D v)) t := by
  exact (((ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt t (hD t))

/-- The fixed vectors of a differentiable one-parameter operator group are
exactly the kernel of its generator. -/
theorem oneParameter_fixed_iff_generator_eq_zero
    {U : ℝ → E →L[ℂ] E} {D : E →L[ℂ] E} (hzero : U 0 = 1)
    (hD : ∀ t, HasDerivAt U (U t * D) t) (v : E) :
    (∀ t, U t v = v) ↔ D v = 0 := by
  constructor
  · intro hv
    have hd := oneParameter_generator_hasDerivAt_apply hD 0 v
    simpa only [hzero, one_apply_eq_self] using
      hd.unique ((hasDerivAt_const 0 v).congr_of_eventuallyEq
        (Filter.Eventually.of_forall hv))
  · intro hv t
    have hd (s : ℝ) : HasDerivAt (fun r => U r v) 0 s := by
      simpa only [hv, map_zero] using oneParameter_generator_hasDerivAt_apply hD s v
    have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa only [hzero, one_apply_eq_self] using hc

/-- Unitarity forces the infinitesimal generator to be skew-adjoint. -/
theorem unitary_oneParameter_generator_skew
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (hzero : U 0 = 1)
    {D : E →L[ℂ] E}
    (hD : ∀ t, HasDerivAt (fun s => (U s).toLinearIsometry.toContinuousLinearMap)
      ((U t).toLinearIsometry.toContinuousLinearMap * D) t) (v w : E) :
    inner ℂ (D v) w = -inner ℂ v (D w) := by
  have hinner := (oneParameter_generator_hasDerivAt_apply hD 0 v).inner ℂ
    (oneParameter_generator_hasDerivAt_apply hD 0 w)
  have hconst : (fun t => inner ℂ (U t v) (U t w)) = fun _ : ℝ => inner ℂ v w := by
    funext t
    exact (U t).inner_map_map v w
  change HasDerivAt (fun t => inner ℂ (U t v) (U t w)) _ 0 at hinner
  rw [hconst] at hinner
  have h := hinner.unique (hasDerivAt_const 0 (inner ℂ v w))
  simp only [hzero,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Multiplication by `i` converts a skew-adjoint generator into the
Hermitian angular-momentum operator used in `Kac/Defs.lean`. -/
theorem imaginary_smul_generator_isSymmetric
    (D : E →L[ℂ] E)
    (hD : ∀ v w, inner ℂ (D v) w = -inner ℂ v (D w)) :
    (Complex.I • D.toLinearMap).IsSymmetric := by
  intro v w
  change inner ℂ (Complex.I • D v) w = inner ℂ v (Complex.I • D w)
  rw [inner_smul_left, inner_smul_right, hD, Complex.conj_I, neg_mul_neg]


/-- A strongly continuous finite-dimensional unitary one-parameter group
has a skew-adjoint generator, and its fixed subspace is the generator kernel. -/
theorem finiteDimensional_unitary_oneParameter_exists_generator
    [FiniteDimensional ℂ E] [CompleteSpace E]
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (hcontinuous : ∀ v, Continuous (fun t => U t v))
    (hzero : U 0 = 1) (hmul : ∀ s t, U (s + t) = U s * U t) :
    ∃ D : E →L[ℂ] E,
      (∀ t, HasDerivAt (fun s => (U s).toLinearIsometry.toContinuousLinearMap)
        ((U t).toLinearIsometry.toContinuousLinearMap * D) t) ∧
      (∀ v w, inner ℂ (D v) w = -inner ℂ v (D w)) ∧
      (∀ v, (∀ t, U t v = v) ↔ D v = 0) := by
  have hcont : Continuous (fun t => (U t).toLinearIsometry.toContinuousLinearMap) :=
    continuous_clm_apply.mpr hcontinuous
  have hz : (U 0).toLinearIsometry.toContinuousLinearMap = 1 := by ext v; simp [hzero]
  have hm (s t : ℝ) : (U (s + t)).toLinearIsometry.toContinuousLinearMap =
      (U s).toLinearIsometry.toContinuousLinearMap * (U t).toLinearIsometry.toContinuousLinearMap := by
    ext v
    simp [hmul]
  obtain ⟨D, hD⟩ := continuous_oneParameter_exists_generator
    (fun t => (U t).toLinearIsometry.toContinuousLinearMap) hcont hz hm
  exact ⟨D, hD, unitary_oneParameter_generator_skew U hzero hD,
    oneParameter_fixed_iff_generator_eq_zero hz hD⟩

end Unitary

end
end GaussianTesting
