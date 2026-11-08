module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GaussianCharacteristic
public import GaussianTesting.Bosons.LinearChange
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-!
# Quadratic Gaussian integrals for physical wavefunctions

The reconstruction of a pure Gaussian wavefunction from its characteristic
function uses the positive momentum block, a real linear diagonalization,
and the finite-dimensional Gaussian Fourier integral. These are analytic
prerequisites for the Gaussian-state characterization in Section 6.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure FourierTransform
open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-- A positive-definite position quadratic form has diagonal coordinates with
strictly positive coefficients and an invertible real coordinate change. -/
theorem positiveQuadratic_diagonal_coordinates {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m)) (hQ : Q.PosDef) :
    ∃ (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m),
      (∀ i, 0 < b i) ∧ ∀ x, Q x = ∑ i, b i * (A x i)^2 := by
  classical
  have hdim : Module.finrank ℝ (WaveConfig m) = m := finrank_euclideanSpace_fin
  have he : ∃ b : Fin m → ℝ, Q.Equivalent (QuadraticMap.weightedSumSquares ℝ b) := by
    have h := Q.equivalent_weightedSumSquares
    rw [hdim] at h
    exact h
  obtain ⟨b, ⟨e⟩⟩ := he
  let A := e.toLinearEquiv.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm
  refine ⟨b, A, ?_, ?_⟩
  · intro i
    have hn : e.symm (Pi.single i 1) ≠ 0 := by
      intro hz
      have h := congrArg e hz
      have : (Pi.single i (1 : ℝ) : Fin m → ℝ) = 0 := by simpa only [map_zero,
        QuadraticMap.IsometryEquiv.apply_symm_apply] using h
      have hi := congrFun this i
      simp only [Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at hi
    have hp := hQ (e.symm (Pi.single i 1)) hn
    rw [← e.map_app, QuadraticMap.IsometryEquiv.apply_symm_apply] at hp
    simpa only [QuadraticMap.weightedSumSquares_apply, Pi.single_apply,
      mul_ite, ite_mul, one_mul, mul_one, mul_zero, zero_mul, smul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hp
  · intro x
    rw [← e.map_app, QuadraticMap.weightedSumSquares_apply]
    simp only [A, ContinuousLinearEquiv.trans_apply, PiLp.coe_symm_continuousLinearEquiv,
      smul_eq_mul, pow_two]
    rfl

/-- The elementary diagonal Gaussian integral in position coordinates, with
an arbitrary complex linear term. -/
theorem integral_diagonal_waveGaussian {m : ℕ} (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (c : Fin m → ℂ) :
    (∫ x : WaveConfig m, Complex.exp
      (-∑ i, (b i : ℂ) * (x i : ℂ)^2 + ∑ i, c i * (x i : ℂ))) =
      ∏ i, (Real.pi / (b i : ℂ)) ^ (1/2 : ℂ) * Complex.exp (c i ^ 2 / (4 * b i)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  exact GaussianFourier.integral_cexp_neg_sum_mul_add (fun i => hb i) c

/-- The same diagonal complex Gaussian is integrable. -/
theorem integrable_diagonal_waveGaussian {m : ℕ} (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (c : Fin m → ℂ) :
    Integrable (fun x : WaveConfig m => Complex.exp
      (-∑ i, (b i : ℂ) * (x i : ℂ)^2 + ∑ i, c i * (x i : ℂ))) := by
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  exact GaussianFourier.integrable_cexp_neg_sum_mul_add (fun i => hb i) c

/-- A real-linear functional on position space is its coordinate sum. -/
theorem waveConfig_linear_eq_sum {m : ℕ} (L : WaveConfig m →ₗ[ℝ] ℂ) (x : WaveConfig m) :
    L x = ∑ i, L (EuclideanSpace.single i 1) * (x i : ℂ) := by
  classical
  have hx : x = ∑ i, x i • EuclideanSpace.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Complex.real_smul, mul_comm]

/-- Change of position coordinates in a complex integral, including its
Jacobian factor. -/
theorem integral_waveCoordinateChange {m : ℕ}
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) (g : WaveConfig m → ℂ) :
    (∫ x, g (A x)) = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • ∫ x, g x := by
  calc
    _ = ∫ x, g x ∂Measure.map A volume :=
      (A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) g).symm
    _ = _ := by rw [linearCoordinateChange_map_volume, integral_smul_measure,
      ENNReal.toReal_ofReal (abs_nonneg _)]

/-- An invertible position change preserves integrability. -/
theorem integrable_waveCoordinateChange {m : ℕ}
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) {g : WaveConfig m → ℂ}
    (hg : Integrable g) : Integrable (fun x => g (A x)) := by
  apply A.toHomeomorph.measurableEmbedding.integrable_map_iff.mp
  change Integrable g (Measure.map A volume)
  rw [linearCoordinateChange_map_volume]
  exact hg.smul_measure ENNReal.ofReal_ne_top

/-- A positive real quadratic exponential remains integrable after adding
any complex real-linear exponent. -/
theorem integrable_quadratic_waveGaussian {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m)) (hQ : Q.PosDef) (L : WaveConfig m →ₗ[ℝ] ℂ) :
    Integrable (fun x => Complex.exp (-(Q x : ℂ) + L x)) := by
  obtain ⟨b, A, hb, hA⟩ := positiveQuadratic_diagonal_coordinates Q hQ
  let c (i : Fin m) := L (A.symm (EuclideanSpace.single i 1))
  have hL (x : WaveConfig m) : L x = ∑ i, c i * (A x i : ℂ) := by
    have h := waveConfig_linear_eq_sum (L.comp A.symm.toLinearMap) (A x)
    change L (A.symm (A x)) = ∑ i, c i * (A x i : ℂ) at h
    rwa [A.symm_apply_apply] at h
  convert integrable_waveCoordinateChange A (integrable_diagonal_waveGaussian b hb c) using 1
  ext x
  rw [hA, hL]
  push_cast
  rfl

/-- The Gaussian integral after diagonalizing its positive real quadratic
part. The arbitrary complex linear term is evaluated on the inverse basis. -/
theorem integral_quadratic_waveGaussian {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m))
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (hb : ∀ i, 0 < b i) (hA : ∀ x, Q x = ∑ i, b i * (A x i)^2)
    (L : WaveConfig m →ₗ[ℝ] ℂ) :
    (∫ x, Complex.exp (-(Q x : ℂ) + L x)) =
      |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
        ∏ i, (Real.pi / (b i : ℂ)) ^ (1/2 : ℂ) *
          Complex.exp ((L (A.symm (EuclideanSpace.single i 1))) ^ 2 / (4 * b i)) := by
  let c (i : Fin m) := L (A.symm (EuclideanSpace.single i 1))
  have hL (x : WaveConfig m) : L x = ∑ i, c i * (A x i : ℂ) := by
    have h := waveConfig_linear_eq_sum (L.comp A.symm.toLinearMap) (A x)
    change L (A.symm (A x)) = ∑ i, c i * (A x i : ℂ) at h
    rwa [A.symm_apply_apply] at h
  have hfun : (fun x => Complex.exp (-(Q x : ℂ) + L x)) =
      fun x => Complex.exp (-∑ i, (b i : ℂ) * (A x i : ℂ)^2 + ∑ i, c i * (A x i : ℂ)) := by
    funext x
    rw [hA, hL]
    push_cast
    rfl
  rw [hfun, integral_waveCoordinateChange A
    (fun x => Complex.exp (-∑ i, (b i : ℂ) * (x i : ℂ)^2 + ∑ i, c i * (x i : ℂ))),
    integral_diagonal_waveGaussian b hb c]

/-- The inverse Fourier transform of a Gaussian with positive real quadratic
part, expressed in the same diagonal coordinates. -/
theorem fourierInv_quadratic_waveGaussian {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m))
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (hb : ∀ i, 0 < b i) (hA : ∀ x, Q x = ∑ i, b i * (A x i)^2)
    (L : WaveConfig m →ₗ[ℝ] ℂ) (x : WaveConfig m) :
    𝓕⁻ (fun t => Complex.exp (-(Q t : ℂ) + L t)) x =
      |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
        ∏ i, (Real.pi / (b i : ℂ)) ^ (1/2 : ℂ) *
          Complex.exp ((L (A.symm (EuclideanSpace.single i 1)) +
            (2 * Real.pi : ℝ) * Complex.I *
              (inner ℝ x (A.symm (EuclideanSpace.single i 1)) : ℂ)) ^ 2 / (4 * b i)) := by
  let L' : WaveConfig m →ₗ[ℝ] ℂ := L + ((2 * Real.pi : ℝ) * Complex.I) •
    (Complex.ofRealCLM.toLinearMap.comp (innerSL ℝ x).toLinearMap)
  have hL' (t : WaveConfig m) : L' t = L t +
      (2 * Real.pi : ℝ) * Complex.I * (inner ℝ x t : ℂ) := rfl
  calc
    _ = ∫ t, Complex.exp (-(Q t : ℂ) + L' t) := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with t
      rw [smul_eq_mul, ← Complex.exp_add, hL', real_inner_comm t x]
      congr 1
      push_cast
      ring
    _ = _ := by
      simpa only [hL'] using integral_quadratic_waveGaussian Q b A hb hA L'

end
end GaussianTesting
