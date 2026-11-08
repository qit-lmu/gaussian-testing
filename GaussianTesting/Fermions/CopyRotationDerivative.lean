module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CopyRotationFixed
public import GaussianTesting.Fermions.CopyRotationGenerators
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Recovering the copy-rotation generator from the Majorana action

The derivative of a strongly continuous finite-dimensional unitary action is
determined by its Majorana commutators and its action on the vacuum. This
identifies the manuscript's second-quantized action with its stated generators,
without leaving a phase ambiguity in the infinitesimal action.
-/

namespace GaussianTesting

open Finset

noncomputable section

variable {n : ℕ} {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Majorana covariance and a fixed vacuum determine the derivative of a
continuous unitary one-parameter action. -/
theorem unitary_oneParameter_deriv_of_majorana_covariance
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (hcont : ∀ v, Continuous (fun t => U t v))
    (hzero : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (C : Fin n → ι → E →ₗ[ℂ] E)
    (hcommutant : ∀ A : E →ₗ[ℂ] E,
      (∀ r a, A * C r a = C r a * A) → ∃ z : ℂ, A = z • LinearMap.id)
    (Ω : E) (hΩ : Ω ≠ 0) (hUΩ : ∀ t, U t Ω = Ω)
    (K : ℝ → Matrix (Fin n) (Fin n) ℝ) (K' : Matrix (Fin n) (Fin n) ℝ)
    (hKzero : K 0 = 1)
    (hK : ∀ r s, HasDerivAt (fun t => K t r s) (K' r s) 0)
    (hcov : ∀ t r a v, U t (C r a v) =
      ∑ s, (K t s r : ℂ) • C s a (U t v))
    (T : E →ₗ[ℂ] E) (hTΩ : T Ω = 0)
    (hT : ∀ r a, T * C r a - C r a * T = ∑ s, (K' s r : ℂ) • C s a) :
    ∀ v, HasDerivAt (fun t => U t v) (T v) 0 := by
  classical
  obtain ⟨D, hD, _, _⟩ := finiteDimensional_unitary_oneParameter_exists_generator
    U hcont hzero hadd
  have hDv (v : E) : HasDerivAt (fun t => U t v) (D v) 0 := by
    simpa [hzero] using oneParameter_generator_hasDerivAt_apply hD 0 v
  have hDC (r : Fin n) (a : ι) :
      D.toLinearMap * C r a - C r a * D.toLinearMap =
        ∑ s, (K' s r : ℂ) • C s a := by
    ext v
    have hc (s : Fin n) : HasDerivAt (fun t => C s a (U t v)) (C s a (D v)) 0 :=
      ((C s a).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hDv v)
    have hs := HasDerivAt.sum (u := (univ : Finset (Fin n)))
      (fun s _ => (hK s r).ofReal_comp.smul (hc s))
    have heq : (fun t => ∑ s, (K t s r : ℂ) • C s a (U t v)) =
        (fun t => U t (C r a v)) := funext (fun t => (hcov t r a v).symm)
    have hs' : HasDerivAt (fun t => U t (C r a v))
        (C r a (D v) + ∑ s, (K' s r : ℂ) • C s a v) 0 := by
      convert hs using 1
      · funext t
        simpa only [Finset.sum_apply, Pi.smul_apply'] using congrFun heq.symm t
      · simp only [hzero, hKzero, Matrix.one_apply,
          Finset.sum_add_distrib]
        simp
    have hd := (hDv (C r a v)).unique hs'
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, ContinuousLinearMap.coe_coe]
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hd)
  have hA (r : Fin n) (a : ι) :
      (D.toLinearMap - T) * C r a = C r a * (D.toLinearMap - T) := by
    have h := (hDC r a).trans (hT r a).symm
    simp only [sub_mul, mul_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  obtain ⟨z, hz⟩ := hcommutant (D.toLinearMap - T) hA
  have hDΩ : D Ω = 0 :=
    (hDv Ω).unique ((hasDerivAt_const 0 Ω).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hUΩ))
  have hzΩ := congrArg (fun A : E →ₗ[ℂ] E => A Ω) hz
  have hz0 : z = 0 := by
    have h : z • Ω = 0 := by simpa [hDΩ, hTΩ] using hzΩ.symm
    exact (smul_eq_zero.mp h).resolve_right hΩ
  have hDT : D.toLinearMap = T := by
    rw [hz0, zero_smul] at hz
    exact sub_eq_zero.mp hz
  intro v
  have he : D v = T v := congrArg (fun A : E →ₗ[ℂ] E => A v) hDT
  rw [← he]
  exact hDv v

end
end GaussianTesting
