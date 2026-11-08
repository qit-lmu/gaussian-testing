module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public section

/-!
# Fourier uniqueness for integrable functions

This is the analytic uniqueness step for recovering density kernels from
bosonic characteristic functions. Fourier inversion on Schwartz test functions
and the Fourier pairing identity imply uniqueness almost everywhere for `L¹`
functions, without any regularity or moment hypothesis.
-/

namespace GaussianTesting

open MeasureTheory FourierTransform
open scoped SchwartzMap InnerProductSpace Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An integrable function with identically zero Fourier transform vanishes
almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero {f : E → ℂ} (hf : Integrable f)
    (hF : ∀ t, 𝓕 f t = 0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  have hG₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hG₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg
  let G : 𝓢(E, ℂ) := hG₁.toSchwartzMap hG₂
  let T : 𝓢(E, ℂ) := 𝓕⁻ G
  have hpair : (∫ x, 𝓕 (T : E → ℂ) x * f x) =
      ∫ x, T x * 𝓕 f x := by
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ E) Real.continuous_fourierChar continuous_inner T.integrable hf)
  have hTG : 𝓕 (T : E → ℂ) = G := by
    rw [← SchwartzMap.fourier_coe]
    exact congrArg (fun h : 𝓢(E, ℂ) => (h : E → ℂ)) (fourier_fourierInv_eq G)
  rw [hTG] at hpair
  change (∫ x, (g x : ℂ) * f x) = ∫ x, T x * 𝓕 f x at hpair
  simpa only [hF, mul_zero, integral_zero, Complex.real_smul] using hpair

/-- Equality of Fourier transforms determines an integrable complex function
up to a null set. -/
theorem ae_eq_of_fourier_eq {f g : E → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hF : ∀ t, 𝓕 f t = 𝓕 g t) : f =ᵐ[volume] g := by
  have hz : (fun x => f x - g x) =ᵐ[volume] 0 :=
    ae_eq_zero_of_fourier_eq_zero (hf.sub hg) (fun t => by
      rw [Real.fourier_eq]
      simp only [smul_sub]
      rw [integral_sub ((Real.fourierIntegral_convergent_iff t).mpr hf)
        ((Real.fourierIntegral_convergent_iff t).mpr hg)]
      exact sub_eq_zero.mpr (hF t))
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

end
end GaussianTesting
