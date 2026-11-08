module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GaussianFourierSlices
public import GaussianTesting.Bosons.GaussianCorrelationPositive

@[expose] public section

/-!
# Gaussian characteristic functions determine Gaussian wavefunctions

The centered Gaussian characteristic function gives integrable Gaussian
Fourier slices of the position correlations. Fourier inversion and uniqueness
recover a continuous quadratic correlation kernel, to which the pure-kernel
reconstruction applies.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure FourierTransform
open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

/-- The positive quadratic momentum block, including the Fourier convention. -/
def gaussianMomentumQuadratic {m : ℕ} (H : QuadraticForm ℝ (WavePhase m)) :
    QuadraticForm ℝ (WaveConfig m) :=
  (4 * Real.pi^2) • H.comp (LinearMap.inr ℝ (WaveConfig m) (WaveConfig m))

theorem gaussianMomentumQuadratic_posDef {m : ℕ} (H : QuadraticForm ℝ (WavePhase m))
    (hH : H.PosDef) : (gaussianMomentumQuadratic H).PosDef := by
  intro t ht
  change 0 < (4 * Real.pi^2) * H (0,t)
  apply mul_pos (by positivity)
  exact hH _ (fun h => ht (congrArg Prod.snd h))

/-- The complex linear exponent in a characteristic-function Fourier slice. -/
def gaussianSliceLinear {m : ℕ} (H : QuadraticForm ℝ (WavePhase m)) (q : WaveConfig m) :
    WaveConfig m →ₗ[ℝ] ℂ :=
  (2 * Real.pi : ℝ) • (Complex.ofRealCLM.toLinearMap.comp
    ((H.polarBilin (q,0)).comp (LinearMap.inr ℝ (WaveConfig m) (WaveConfig m)))) -
  ((Real.pi : ℂ) * Complex.I) •
    (Complex.ofRealCLM.toLinearMap.comp (innerSL ℝ q).toLinearMap)

theorem gaussianSliceLinear_apply {m : ℕ} (H : QuadraticForm ℝ (WavePhase m))
    (q t : WaveConfig m) : gaussianSliceLinear H q t =
      (2 * Real.pi : ℝ) * (H.polarBilin (q,0) (0,t) : ℂ) -
        (Real.pi : ℂ) * Complex.I * (inner ℝ q t : ℂ) := rfl

private theorem gaussian_slice_exponent {m : ℕ} (H : QuadraticForm ℝ (WavePhase m))
    (q t : WaveConfig m) :
    -(H (q,(-2 * Real.pi) • t) : ℂ) - Complex.I * (Real.pi * inner ℝ q t : ℝ) =
      -(H (q,0) : ℂ) - (gaussianMomentumQuadratic H t : ℂ) + gaussianSliceLinear H q t := by
  have hsum : (q,(-2 * Real.pi) • t) = (q,0) + (-2 * Real.pi) • (0,t) := by simp
  rw [hsum, QuadraticMap.map_add H (q,0) ((-2 * Real.pi) • (0,t)),
    ← QuadraticMap.polarBilin_apply_apply]
  simp only [QuadraticMap.map_smul, LinearMap.map_smul, smul_eq_mul,
    gaussianMomentumQuadratic, _root_.smul_apply, QuadraticMap.comp_apply,
    LinearMap.inr_apply, gaussianSliceLinear_apply]
  push_cast
  ring

/-- The Fourier slice of a centered Gaussian pure characteristic function. -/
theorem gaussian_correlation_fourier {m : ℕ} (f : WaveSpace m)
    (H : QuadraticForm ℝ (WavePhase m))
    (hχ : ∀ r, pureWaveCharacteristic m f r = Complex.exp (-(H r : ℂ)))
    (q t : WaveConfig m) :
    𝓕 (waveCorrelation f q) t = Complex.exp (-(H (q,0) : ℂ)) *
      Complex.exp (-(gaussianMomentumQuadratic H t : ℂ) + gaussianSliceLinear H q t) := by
  have h := pureWaveCharacteristic_fourier f q t
  rw [hχ] at h
  have he : Complex.exp (-Complex.I * (inner ℝ ((-2 * Real.pi) • t) q : ℂ) / 2) =
      Complex.exp (Complex.I * (Real.pi * inner ℝ q t : ℝ)) := by
    congr 1
    rw [real_inner_smul_left, real_inner_comm t q]
    push_cast
    ring
  rw [he] at h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (Complex.I * (Real.pi * inner ℝ q t : ℝ)))
  rw [← h, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hh := gaussian_slice_exponent H q t
  linear_combination hh

/-- The joint linear coefficient in the inverse Fourier Gaussian integral. -/
def gaussianKernelLinear {m : ℕ} (H : QuadraticForm ℝ (WavePhase m)) (v : WaveConfig m) :
    WavePhase m →ₗ[ℝ] ℂ :=
  (2 * Real.pi : ℝ) • (Complex.ofRealCLM.toLinearMap.comp
    ((H.polarBilin.flip (0,v)).comp
      ((LinearMap.inl ℝ (WaveConfig m) (WaveConfig m)).comp
        (LinearMap.fst ℝ (WaveConfig m) (WaveConfig m))))) -
  ((Real.pi : ℂ) * Complex.I) • (Complex.ofRealCLM.toLinearMap.comp
    ((innerSL ℝ v).toLinearMap.comp (LinearMap.fst ℝ (WaveConfig m) (WaveConfig m)))) +
  ((2 * Real.pi : ℝ) * Complex.I) • (Complex.ofRealCLM.toLinearMap.comp
    ((innerSL ℝ v).toLinearMap.comp (LinearMap.snd ℝ (WaveConfig m) (WaveConfig m))))

theorem gaussianKernelLinear_apply {m : ℕ} (H : QuadraticForm ℝ (WavePhase m))
    (v q x : WaveConfig m) : gaussianKernelLinear H v (q,x) =
      gaussianSliceLinear H q v + (2 * Real.pi : ℝ) * Complex.I * (inner ℝ x v : ℂ) := by
  simp only [gaussianKernelLinear, gaussianSliceLinear_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.inl_apply, LinearMap.flip_apply,
    ContinuousLinearMap.coe_coe, Complex.ofRealCLM_apply, innerSL_apply_apply,
    smul_eq_mul, real_inner_comm, Complex.real_smul]

/-- The homogeneous quadratic kernel produced by the Gaussian Fourier integral. -/
def gaussianCorrelationQuadratic {m : ℕ} (H : QuadraticForm ℝ (WavePhase m))
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    QuadraticMap ℝ (WavePhase m) ℂ :=
  -(Complex.ofRealCLM.toLinearMap.compQuadraticMap (H.comp
    ((LinearMap.inl ℝ (WaveConfig m) (WaveConfig m)).comp
      (LinearMap.fst ℝ (WaveConfig m) (WaveConfig m))))) +
  ∑ i, (1 / (4 * (b i : ℂ))) • QuadraticMap.linMulLin
    (gaussianKernelLinear H (A.symm (EuclideanSpace.single i 1)))
    (gaussianKernelLinear H (A.symm (EuclideanSpace.single i 1)))

theorem gaussianCorrelationQuadratic_apply {m : ℕ} (H : QuadraticForm ℝ (WavePhase m))
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) (q x : WaveConfig m) :
    gaussianCorrelationQuadratic H b A (q,x) = -(H (q,0) : ℂ) +
      ∑ i, (gaussianSliceLinear H q (A.symm (EuclideanSpace.single i 1)) +
        (2 * Real.pi : ℝ) * Complex.I *
          (inner ℝ x (A.symm (EuclideanSpace.single i 1)) : ℂ))^2 / (4 * b i) := by
  simp [gaussianCorrelationQuadratic, gaussianKernelLinear_apply, QuadraticMap.linMulLin_apply,
    pow_two, div_eq_mul_inv, mul_comm]

/-- Continuity of the explicit quadratic correlation kernel. -/
theorem continuous_gaussianCorrelationQuadratic {m : ℕ}
    (H : QuadraticForm ℝ (WavePhase m)) (hH : Continuous H)
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    Continuous (gaussianCorrelationQuadratic H b A) := by
  have hlinear (i : Fin m) : Continuous
      (gaussianKernelLinear H (A.symm (EuclideanSpace.single i 1))) :=
    LinearMap.continuous_of_finiteDimensional _
  have hfun : (gaussianCorrelationQuadratic H b A : WavePhase m → ℂ) =
      fun z => -(H (z.1,0) : ℂ) + ∑ i,
        (1 / (4 * (b i : ℂ))) * (gaussianKernelLinear H
          (A.symm (EuclideanSpace.single i 1)) z)^2 := by
    funext z
    simp [gaussianCorrelationQuadratic, QuadraticMap.linMulLin_apply, pow_two]
  rw [hfun]
  fun_prop

/-- On the diagonal, the correlation kernel has exactly the positive dual
quadratic decay of the Gaussian Fourier transform. -/
theorem gaussianCorrelationQuadratic_zero_re {m : ℕ}
    (H : QuadraticForm ℝ (WavePhase m))
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m) (x : WaveConfig m) :
    (gaussianCorrelationQuadratic H b A (0,x)).re = -waveGaussianDualQuadratic b A x := by
  have hlin (v : WaveConfig m) : gaussianSliceLinear H 0 v = 0 := by
    simp [gaussianSliceLinear_apply, QuadraticMap.polar,
      show H ((0 : WaveConfig m), 0) = 0 from H.map_zero]
  have he : gaussianCorrelationQuadratic H b A (0,x) =
      -(waveGaussianDualQuadratic b A x : ℂ) := by
    rw [gaussianCorrelationQuadratic_apply, waveGaussianDualQuadratic_apply]
    simp only [hlin, zero_add, show H ((0 : WaveConfig m), 0) = 0 from map_zero H,
      Complex.ofReal_zero, neg_zero, Complex.ofReal_sum]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he, Complex.neg_re, Complex.ofReal_re]

/-- The nonzero normalization factor in the reconstructed Gaussian kernel. -/
def gaussianCorrelationConstant {m : ℕ} (b : Fin m → ℝ)
    (A : WaveConfig m ≃L[ℝ] WaveConfig m) : ℂ :=
  (|(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| : ℝ) *
    ∏ i, (Real.pi / (b i : ℂ)) ^ (1/2 : ℂ)

theorem gaussianCorrelationConstant_ne_zero {m : ℕ} (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (A : WaveConfig m ≃L[ℝ] WaveConfig m) :
    gaussianCorrelationConstant b A ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr
      (inv_ne_zero (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero))
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (Complex.ofReal_ne_zero.mpr (hb i).ne')

private theorem fourierInv_complex_const_mul {m : ℕ} (c : ℂ) (g : WaveConfig m → ℂ)
    (x : WaveConfig m) :
    𝓕⁻ (fun t => c * g t) x = c * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  simp only [smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul c _

/-- The inverse Fourier slice has one common quadratic kernel and a nonzero
constant independent of the position displacement. -/
theorem gaussian_correlation_fourierInv {m : ℕ}
    (H : QuadraticForm ℝ (WavePhase m))
    (b : Fin m → ℝ) (A : WaveConfig m ≃L[ℝ] WaveConfig m)
    (hb : ∀ i, 0 < b i)
    (hA : ∀ t, gaussianMomentumQuadratic H t = ∑ i, b i * (A t i)^2)
    (q x : WaveConfig m) :
    𝓕⁻ (fun t => Complex.exp (-(H (q,0) : ℂ)) *
      Complex.exp (-(gaussianMomentumQuadratic H t : ℂ) + gaussianSliceLinear H q t)) x =
      gaussianCorrelationConstant b A * Complex.exp (gaussianCorrelationQuadratic H b A (q,x)) := by
  rw [fourierInv_complex_const_mul]
  rw [fourierInv_quadratic_waveGaussian (gaussianMomentumQuadratic H) b A hb hA,
    gaussianCorrelationQuadratic_apply]
  simp only [Finset.prod_mul_distrib, ← Complex.exp_sum, Complex.real_smul,
    gaussianCorrelationConstant, Complex.exp_add]
  ring

/-- Fourier uniqueness recovers the explicit quadratic correlations of every
actual centered Gaussian pure characteristic function. -/
theorem gaussian_correlation_eq {m : ℕ} (f : WaveSpace m)
    (H : QuadraticForm ℝ (WavePhase m)) (hH : H.PosDef) (hHcont : Continuous H)
    (hχ : ∀ r, pureWaveCharacteristic m f r = Complex.exp (-(H r : ℂ))) :
    ∃ (R : QuadraticMap ℝ (WavePhase m) ℂ) (C : ℂ) (B : QuadraticForm ℝ (WaveConfig m)),
      Continuous R ∧ C ≠ 0 ∧ B.PosDef ∧
      (∀ q, waveCorrelation f q =ᵐ[volume] fun x => C * Complex.exp (R (q,x))) ∧
      (∀ x, (R (0,x)).re = -B x) := by
  let M := gaussianMomentumQuadratic H
  have hM : M.PosDef := gaussianMomentumQuadratic_posDef H hH
  obtain ⟨b, A, hb, hA⟩ := positiveQuadratic_diagonal_coordinates M hM
  refine ⟨gaussianCorrelationQuadratic H b A, gaussianCorrelationConstant b A,
    waveGaussianDualQuadratic b A, continuous_gaussianCorrelationQuadratic H hHcont b A,
    gaussianCorrelationConstant_ne_zero b hb A, waveGaussianDualQuadratic_posDef b hb A,
    ?_, gaussianCorrelationQuadratic_zero_re H b A⟩
  intro q
  let G (t : WaveConfig m) := Complex.exp (-(H (q,0) : ℂ)) *
    Complex.exp (-(M t : ℂ) + gaussianSliceLinear H q t)
  have hG : Integrable G :=
    (integrable_quadratic_waveGaussian M hM (gaussianSliceLinear H q)).const_mul _
  have hiG : Integrable (𝓕⁻ G) := by
    have h := (integrable_fourierInv_quadratic_waveGaussian M hM
      (gaussianSliceLinear H q)).const_mul (Complex.exp (-(H (q,0) : ℂ)))
    have heq : 𝓕⁻ G = fun x => Complex.exp (-(H (q,0) : ℂ)) *
        𝓕⁻ (fun t => Complex.exp (-(M t : ℂ) + gaussianSliceLinear H q t)) x :=
      funext (fourierInv_complex_const_mul _ _)
    rw [heq]
    exact h
  have hcG : Continuous G := by
    have hL := (gaussianSliceLinear H q).continuous_of_finiteDimensional
    have hcontM : Continuous M := by
      change Continuous (fun t => (4 * Real.pi^2) • H (0,t))
      fun_prop
    dsimp [G]
    fun_prop
  have hFG : Integrable (𝓕 G) := by
    simpa only [Function.comp_apply, Real.fourierInv_eq_fourier_neg, neg_neg] using hiG.comp_neg
  have hF : 𝓕 (𝓕⁻ G) = G := hcG.fourier_fourierInv_eq hG hFG
  have hcorr : waveCorrelation f q =ᵐ[volume] 𝓕⁻ G := by
    apply ae_eq_of_fourier_eq (integrable_waveCorrelation f q) hiG
    intro t
    rw [hF]
    exact gaussian_correlation_fourier f H hχ q t
  have hexp : 𝓕⁻ G = fun x => gaussianCorrelationConstant b A *
      Complex.exp (gaussianCorrelationQuadratic H b A (q,x)) := by
    funext x
    exact gaussian_correlation_fourierInv H b A hb hA q x
  rwa [hexp] at hcorr

/-- A physical unit pure state with a centered Gaussian characteristic
function is a symplectic-vacuum state, up to its irrelevant unit phase. -/
theorem exists_symplectic_vacuum_of_centered_gaussian_characteristic {m : ℕ}
    (f : WaveSpace m) (hf : ‖f‖ = 1)
    (H : QuadraticForm ℝ (WavePhase m)) (hH : H.PosDef) (hHcont : Continuous H)
    (hχ : ∀ r, pureWaveCharacteristic m f r = Complex.exp (-(H r : ℂ))) :
    ∃ (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
      (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (z : ℂ),
      ‖z‖ = 1 ∧ f = z • waveSymplecticUnitary S hS (waveVacuum m) := by
  obtain ⟨R,C,B,hR,hC,hB,hcorr,hdiag⟩ := gaussian_correlation_eq f H hH hHcont hχ
  exact exists_symplectic_vacuum_of_gaussian_correlation f hf R hR C hC hcorr B hB hdiag

/-- The centered Gaussian-characteristic conclusion used in Proposition 6.1
identifies the actual unit wavefunction with the symplectic vacuum orbit.
Strict positivity of the covariance exponent is derived from the physical
Weyl action and is not an additional hypothesis. -/
theorem exists_symplectic_vacuum_of_pureCharacteristic_quadratic {m : ℕ}
    (f : WaveSpace m) (hf : ‖f‖ = 1)
    (Q : QuadraticForm ℝ (WavePhase m)) (hQcont : Continuous Q)
    (hχ : ∀ r, pureWaveCharacteristic m f r = (Real.exp (Q r) : ℂ)) :
    ∃ (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
      (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (z : ℂ),
      ‖z‖ = 1 ∧ f = z • waveSymplecticUnitary S hS (waveVacuum m) := by
  have hformula : ∀ r, pureWaveCharacteristic m f r =
      Complex.exp ((Q r : ℂ) + Complex.I * ((0 : WavePhase m →L[ℝ] ℝ) r : ℂ)) := by
    intro r
    simpa only [_root_.zero_apply, Complex.ofReal_zero, mul_zero,
      add_zero, Complex.ofReal_exp] using hχ r
  have hpos := gaussianCharacteristic_neg_posDef f hf Q 0 hformula
  apply exists_symplectic_vacuum_of_centered_gaussian_characteristic f hf (-Q) hpos hQcont.neg
  intro r
  simpa only [_root_.neg_apply, Complex.ofReal_neg, neg_neg, Complex.ofReal_exp] using hχ r

/-- A Gaussian characteristic function with a linear phase comes from an
actual displaced symplectic vacuum, up to a unit complex scalar. This direction
requires neither moment assumptions nor an assumed nonsingular covariance. -/
theorem exists_displaced_symplectic_vacuum_of_gaussian_characteristic {m : ℕ}
    (f : WaveSpace m) (hf : ‖f‖ = 1)
    (Q : QuadraticForm ℝ (WavePhase m)) (hQcont : Continuous Q)
    (L : WavePhase m →L[ℝ] ℝ)
    (hχ : ∀ r, pureWaveCharacteristic m f r =
      Complex.exp ((Q r : ℂ) + Complex.I * (L r : ℂ))) :
    ∃ (a : WavePhase m) (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
      (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (z : ℂ),
      ‖z‖ = 1 ∧ f = z • weylOperator m a (waveSymplecticUnitary S hS (waveVacuum m)) := by
  obtain ⟨a, hnorm, hcenter⟩ := gaussianCharacteristic_centered_by_displacement f hf Q L hχ
  obtain ⟨S, hS, z, hz, heq⟩ := exists_symplectic_vacuum_of_pureCharacteristic_quadratic
    (weylOperator m (-a) f) hnorm Q hQcont hcenter
  refine ⟨a, S, hS, z, hz, ?_⟩
  have h := congrArg (weylOperator m a) heq
  simpa only [weylOperator_neg_right, map_smul] using h

end
end GaussianTesting
