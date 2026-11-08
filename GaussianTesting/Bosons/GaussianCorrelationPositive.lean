module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GaussianKernelReconstruction
public import GaussianTesting.Bosons.WaveGaussianOrbit

@[expose] public section

/-!
# Strict decay of the wavefunction reconstructed from Gaussian correlations

The diagonal of a pure-state kernel is its squared modulus. Comparing this
identity at an arbitrary position and at the origin transfers strict decay of
the diagonal Gaussian kernel to the real part of the wavefunction exponent.
-/

namespace GaussianTesting

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true

/-- Strict decay of the diagonal Gaussian correlation gives a homogeneous
quadratic wavefunction with negative definite real exponent. -/
theorem positive_definite_wavefunction_of_gaussian_correlation {m : ℕ}
    (f : WaveSpace m) (R : QuadraticMap ℝ (WavePhase m) ℂ) (hR : Continuous R)
    (C : ℂ) (hC : C ≠ 0)
    (hcorr : ∀ q, waveCorrelation f q =ᵐ[volume] fun x => C * Complex.exp (R (q,x)))
    (B : QuadraticForm ℝ (WaveConfig m)) (hB : B.PosDef)
    (hdiag : ∀ x, (R (0,x)).re = -B x) :
    ∃ Q : QuadraticMap ℝ (WaveConfig m) ℂ,
      (-Complex.reCLM.toLinearMap.compQuadraticMap Q).PosDef ∧
      ∃ c : ℂ, c ≠ 0 ∧ f =ᵐ[volume] fun x => c * Complex.exp (Q x) := by
  let e : WaveConfig m →ₗ[ℝ] WavePhase m :=
    (-LinearMap.id : WaveConfig m →ₗ[ℝ] WaveConfig m).prod 0
  let Q := R.comp e
  have hQ (x : WaveConfig m) : Q x = R (-x,0) := rfl
  have hQc : Continuous Q := by
    change Continuous (fun x : WaveConfig m => R (-x,0))
    exact hR.comp (continuous_neg.prodMk continuous_const)
  obtain ⟨c, hc, hf⟩ := wavefunction_of_gaussian_correlation f R hR C hC hcorr
  have heq : ∀ x : WaveConfig m,
      inner ℂ (c * Complex.exp (Q x)) (c * Complex.exp (Q x)) =
        C * Complex.exp (R (0,x)) := by
    have hae :
        (fun x : WaveConfig m => inner ℂ (c * Complex.exp (Q x)) (c * Complex.exp (Q x)))
          =ᵐ[volume] fun x => C * Complex.exp (R (0,x)) := by
      filter_upwards [hcorr 0, hf] with x hx hy
      simpa only [waveCorrelation, sub_zero, hy, hQ] using hx
    exact congrFun (Measure.eq_of_ae_eq (μ := volume) hae
      (by fun_prop) (by fun_prop))
  have hcn : ‖C‖ = ‖c‖ ^ 2 := by
    have h := congrArg norm (heq 0)
    have hz : R (0,0) = 0 := R.map_zero
    simpa [hz, inner_self_eq_norm_sq_to_K] using h.symm
  have hexponent (x : WaveConfig m) : 2 * (Q x).re = -B x := by
    have h := congrArg norm (heq x)
    rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq, norm_mul, Complex.norm_exp, mul_pow, norm_mul,
      Complex.norm_exp, hcn, hdiag] at h
    have hn : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
    have hh := mul_left_cancel₀ hn h
    rw [← Real.exp_nat_mul] at hh
    exact Real.exp_injective (by simpa only [Nat.cast_ofNat] using hh)
  refine ⟨Q, ?_, c, hc, ?_⟩
  · intro x hx
    change 0 < -(Q x).re
    have hb := hB x hx
    have hh := hexponent x
    linarith
  · simpa only [hQ] using hf

/-- The analytic Gaussian-correlation reconstruction places a normalized pure
state in the symplectic vacuum orbit. -/
theorem exists_symplectic_vacuum_of_gaussian_correlation {m : ℕ}
    (f : WaveSpace m) (hf : ‖f‖ = 1)
    (R : QuadraticMap ℝ (WavePhase m) ℂ) (hR : Continuous R) (C : ℂ) (hC : C ≠ 0)
    (hcorr : ∀ q, waveCorrelation f q =ᵐ[volume] fun x => C * Complex.exp (R (q,x)))
    (B : QuadraticForm ℝ (WaveConfig m)) (hB : B.PosDef)
    (hdiag : ∀ x, (R (0,x)).re = -B x) :
    ∃ (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
      (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (z : ℂ),
      ‖z‖ = 1 ∧ f = z • waveSymplecticUnitary S hS (waveVacuum m) := by
  obtain ⟨Q, hQ, c, _, hfun⟩ :=
    positive_definite_wavefunction_of_gaussian_correlation f R hR C hC hcorr B hB hdiag
  exact exists_symplectic_vacuum_of_quadratic_wavefunction Q hQ f hf c hfun

end
end GaussianTesting
