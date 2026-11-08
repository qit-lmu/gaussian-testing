module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PhysicalMeanZero
public import GaussianTesting.Bosons.InvariantQuadratic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Polynomial Gaussian vectors in the closed span of Gaussian squares

Identical quadratic phase multipliers preserve the centered Gaussian states.
Differentiating their matrix coefficients shows that their closed square span
is stable under multiplication by the two-copy Gram quadratics. The required
domination follows from the square-integrability of polynomial Gaussian vectors.
-/

namespace GaussianTesting

open MeasureTheory Filter MvPolynomial
open scoped InnerProductSpace Topology ComplexConjugate

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The closed span of squares of the independently defined centered Gaussian
wavefunctions, in the actual two-copy Schrödinger space. -/
def meanZeroGaussianSquareSpan (m : ℕ) : Submodule ℂ (SchrodingerSpace m) :=
  (Submodule.span ℂ ((fun ψ => waveTensorEquiv m (hilbertTmul ψ ψ)) ''
    meanZeroGaussianWaveStates m)).topologicalClosure

theorem isClosed_meanZeroGaussianSquareSpan (m : ℕ) :
    IsClosed (meanZeroGaussianSquareSpan m : Set (SchrodingerSpace m)) :=
  Submodule.isClosed_topologicalClosure _

theorem gaussianSquare_mem_meanZeroGaussianSquareSpan {m : ℕ} {ψ : WaveSpace m}
    (hψ : ψ ∈ meanZeroGaussianWaveStates m) :
    waveTensorEquiv m (hilbertTmul ψ ψ) ∈ meanZeroGaussianSquareSpan m :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ψ, hψ, rfl⟩)

private theorem phase_matrixCoefficient_hasDerivAt {m : ℕ}
    (a : C(BosonConfig m, ℝ)) (f g h : SchrodingerSpace m)
    (hh : (h : BosonConfig m → ℂ) =ᵐ[volume] fun z => (a z : ℂ) * g z) :
    HasDerivAt (fun t : ℝ => inner ℂ f (schrodingerPhaseMultiplier (t • a) g))
      (Complex.I * inner ℂ f h) 0 := by
  let F (t : ℝ) (z : BosonConfig m) : ℂ :=
    inner ℂ (f z) (Complex.exp (Complex.I * ((t * a z : ℝ) : ℂ)) * g z)
  let F' (t : ℝ) (z : BosonConfig m) : ℂ :=
    inner ℂ (f z) (Complex.exp (Complex.I * ((t * a z : ℝ) : ℂ)) *
      (Complex.I * (a z : ℂ) * g z))
  have hphase (t : ℝ) : Continuous (fun z : BosonConfig m =>
      Complex.exp (Complex.I * ((t * a z : ℝ) : ℂ))) := by fun_prop
  have hFmeas (t : ℝ) : AEStronglyMeasurable (F t) volume :=
    (Lp.aestronglyMeasurable f).inner
      ((hphase t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
  have hF'meas (t : ℝ) : AEStronglyMeasurable (F' t) volume := by
    apply (Lp.aestronglyMeasurable f).inner
    exact (hphase t).aestronglyMeasurable.mul
      (((Complex.continuous_ofReal.comp a.continuous).const_mul Complex.I).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable g))
  have hFint : Integrable (F 0) volume := by
    simpa only [F, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using
      L2.integrable_inner f g
  have hbound : ∀ᵐ z ∂volume, ∀ t ∈ (Set.univ : Set ℝ),
      ‖F' t z‖ ≤ ‖inner ℂ (f z) (h z)‖ := by
    filter_upwards [hh] with z hz
    intro t _
    rw [hz]
    simp only [F', RCLike.inner_apply, norm_mul,
      Complex.norm_exp_I_mul_ofReal, Complex.norm_I, one_mul]
    exact le_of_eq (by ring)
  have hdiff : ∀ᵐ z ∂volume, ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun t => F t z) (F' t z) t := by
    apply ae_of_all
    intro z t _
    have ht := (((hasDerivAt_id t).mul_const (a z)).ofReal_comp.const_mul
      Complex.I).cexp.mul_const (g z)
    have ht' := ht.const_mul (star (f z))
    simpa only [F, F', RCLike.inner_apply, one_mul, mul_assoc, mul_comm,
      mul_left_comm, id_eq, starRingEnd_apply] using ht'
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Set.univ) (bound := fun z => ‖inner ℂ (f z) (h z)‖)
    (by simp) (Eventually.of_forall hFmeas) hFint (hF'meas 0)
    hbound (L2.integrable_inner f h).norm hdiff
  have heq (t : ℝ) : (∫ z, F t z) =
      inner ℂ f (schrodingerPhaseMultiplier (t • a) g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [schrodingerPhaseMultiplier_coeFn (t • a) g] with z hz
    simp only [ContinuousMap.smul_apply, smul_eq_mul] at hz
    rw [hz]
  have hdeq : (∫ z, F' 0 z) = Complex.I * inner ℂ f h := by
    rw [L2.inner_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hh] with z hz
    simp [F', hz, RCLike.inner_apply, mul_assoc, mul_left_comm]
  simpa only [heq, hdeq] using hd

private theorem mem_of_phase_invariant {m : ℕ} (W : Submodule ℂ (SchrodingerSpace m))
    (hW : IsClosed (W : Set (SchrodingerSpace m))) (a : C(BosonConfig m, ℝ))
    (hphase : ∀ t : ℝ, ∀ g ∈ W, schrodingerPhaseMultiplier (t • a) g ∈ W)
    (g h : SchrodingerSpace m) (hg : g ∈ W)
    (hh : (h : BosonConfig m → ℂ) =ᵐ[volume] fun z => (a z : ℂ) * g z) : h ∈ W := by
  rw [← hW.submodule_topologicalClosure_eq, ← W.orthogonal_orthogonal_eq_closure]
  apply (W.orthogonal.mem_orthogonal h).mpr
  intro f hf
  have hzero (t : ℝ) : inner ℂ f (schrodingerPhaseMultiplier (t • a) g) = 0 :=
    (W.mem_orthogonal' f).mp hf _ (hphase t g hg)
  have hd := phase_matrixCoefficient_hasDerivAt a f g h hh
  simp only [hzero] at hd
  have he := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  exact (mul_eq_zero.mp he).resolve_left Complex.I_ne_zero

private theorem quadraticPhase_mem_meanZeroGaussianWaveStates {m : ℕ}
    (A : WaveConfig m →L[ℝ] WaveConfig m) {ψ : WaveSpace m}
    (hψ : ψ ∈ meanZeroGaussianWaveStates m) :
    waveQuadraticPhase m A ψ ∈ meanZeroGaussianWaveStates m := by
  have hn := norm_eq_one_of_mem_meanZeroGaussianWaveStates hψ
  have hfix := (schrodingerTensorP0_fixed_iff_meanZeroGaussianWaveStates ψ hn).mpr hψ
  apply (schrodingerTensorP0_fixed_iff_meanZeroGaussianWaveStates _
    (by simpa using hn)).mp
  have h := (quadraticPhase_commutesWithCopyRotations m A).tensorP0 (hilbertTmul ψ ψ)
  rw [hfix, diagonalWaveAction_tmul] at h
  exact h.symm

private theorem quadraticPhase_mem_squareSpan {m : ℕ}
    (A : WaveConfig m →L[ℝ] WaveConfig m) {f : SchrodingerSpace m}
    (hf : f ∈ meanZeroGaussianSquareSpan m) :
    schrodingerPhaseMultiplier (twoCopyQuadraticForm m A) f ∈
      meanZeroGaussianSquareSpan m := by
  let U := (schrodingerPhaseMultiplier (twoCopyQuadraticForm m A)).toLinearIsometry.toContinuousLinearMap
  let S := Submodule.span ℂ ((fun ψ => waveTensorEquiv m (hilbertTmul ψ ψ)) ''
    meanZeroGaussianWaveStates m)
  have hUS : S ≤ S.comap U.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ψ, hψ, rfl⟩
    change schrodingerPhaseMultiplier (twoCopyQuadraticForm m A)
      (waveTensorEquiv m (hilbertTmul ψ ψ)) ∈ S
    rw [waveTensorEquiv_apply, ← waveTensor_quadraticPhase, hilbertTensorMap_tmul]
    apply Submodule.subset_span
    exact ⟨waveQuadraticPhase m A ψ, quadraticPhase_mem_meanZeroGaussianWaveStates A hψ, rfl⟩
  have hmap : S.map U.toLinearMap ≤ S := Submodule.map_le_iff_le_comap.mpr hUS
  have hclosure := (S.topologicalClosure_map U).trans (Submodule.topologicalClosure_mono hmap)
  exact hclosure ⟨f, hf, rfl⟩

private def gramFormMap {m : ℕ} (i j : Fin m) : WaveConfig m →L[ℝ] WaveConfig m :=
  (PiLp.proj 2 (fun _ : Fin m => ℝ) j).smulRight (EuclideanSpace.single i 2)

private theorem gramFormMap_inner {m : ℕ} (i j : Fin m) (x : WaveConfig m) :
    inner ℝ x (gramFormMap i j x) / 2 = x i * x j := by
  simp only [gramFormMap, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
    inner_smul_right, EuclideanSpace.inner_single_right, conj_trivial]
  ring

private theorem twoCopyQuadraticForm_smul {m : ℕ}
    (A : WaveConfig m →L[ℝ] WaveConfig m) (t : ℝ) :
    twoCopyQuadraticForm m (t • A) = t • twoCopyQuadraticForm m A := by
  ext z
  simp only [twoCopyQuadraticForm, ContinuousMap.coe_mk, smul_apply,
    inner_smul_right, ContinuousMap.smul_apply, smul_eq_mul]
  ring

private theorem eval_copyGramPolynomial {m : ℕ} (i j : Fin m) (z : BosonConfig m) :
    eval (fun k => (z k : ℂ)) (copyGramPolynomial m i j) =
      (twoCopyQuadraticForm m (gramFormMap i j) z : ℂ) := by
  simp only [copyGramPolynomial, eval_add, eval_mul, eval_X, twoCopyQuadraticForm,
    ContinuousMap.coe_mk, gramFormMap_inner, Complex.ofReal_add, Complex.ofReal_mul]
  rfl

private theorem gram_mul_mem_squareSpan {m : ℕ} (i j : Fin m)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ)
    (hp : polynomialGaussian p ∈ meanZeroGaussianSquareSpan m) :
    polynomialGaussian (copyGramPolynomial m i j * p) ∈ meanZeroGaussianSquareSpan m := by
  apply mem_of_phase_invariant (meanZeroGaussianSquareSpan m)
    (isClosed_meanZeroGaussianSquareSpan m) (twoCopyQuadraticForm m (gramFormMap i j))
    (fun t g hg => ?_) (polynomialGaussian p) _ hp
  · filter_upwards [polynomialGaussian_coeFn (copyGramPolynomial m i j * p),
      polynomialGaussian_coeFn p] with z hz hpz
    rw [hz, hpz]
    simp only [polynomialGaussianFun, eval_mul, eval_copyGramPolynomial, mul_assoc]
  · rw [← twoCopyQuadraticForm_smul]
    exact quadraticPhase_mem_squareSpan _ hg

private theorem polynomialGaussian_one_mem_squareSpan (m : ℕ) :
    polynomialGaussian (1 : MvPolynomial (Fin 2 × Fin m) ℂ) ∈ meanZeroGaussianSquareSpan m := by
  have hvac : waveVacuum m ∈ meanZeroGaussianWaveStates m :=
    (schrodingerTensorP0_fixed_iff_meanZeroGaussianWaveStates _ (waveVacuum_norm m)).mp
      (schrodingerTensorP0_vacuum m)
  let c : ℂ := ((Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ) ^ 2
  have hc : c ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)))
  have heq : waveTensorEquiv m (hilbertTmul (waveVacuum m) (waveVacuum m)) =
      c • polynomialGaussian (1 : MvPolynomial (Fin 2 × Fin m) ℂ) := by
    apply Lp.ext
    filter_upwards [waveTensor_vacuum_coeFn m,
      Lp.coeFn_smul c (polynomialGaussian (1 : MvPolynomial (Fin 2 × Fin m) ℂ)),
      polynomialGaussian_coeFn (1 : MvPolynomial (Fin 2 × Fin m) ℂ)] with z hz hs hp
    simp only [waveTensorEquiv_apply, hz, hs, Pi.smul_apply, smul_eq_mul,
      hp, polynomialGaussianFun, map_one, one_mul, c]
  exact (Submodule.smul_mem_iff _ hc).mp
    (heq ▸ gaussianSquare_mem_meanZeroGaussianSquareSpan hvac)

/-- Every polynomial in the two-copy Gram entries, multiplied by the vacuum
Gaussian, belongs to the closed span of centered Gaussian squares. -/
theorem polynomialGaussian_mem_meanZeroGaussianSquareSpan {m : ℕ}
    {p : MvPolynomial (Fin 2 × Fin m) ℂ} (hp : p ∈ copyGramAlgebra m) :
    polynomialGaussian p ∈ meanZeroGaussianSquareSpan m := by
  have hstable : ∀ p ∈ copyGramAlgebra m,
      ∀ q : MvPolynomial (Fin 2 × Fin m) ℂ,
        polynomialGaussian q ∈ meanZeroGaussianSquareSpan m →
        polynomialGaussian (p * q) ∈ meanZeroGaussianSquareSpan m := by
    intro p hp
    induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨⟨i,j⟩, rfl⟩ := hp
      exact fun q hq => gram_mul_mem_squareSpan i j q hq
    | algebraMap c =>
      intro q hq
      change polynomialGaussian (C c * q) ∈ _
      rw [← MvPolynomial.smul_eq_C_mul, polynomialGaussian_smul]
      exact (meanZeroGaussianSquareSpan m).smul_mem c hq
    | add p₁ p₂ _ _ h₁ h₂ =>
      intro q hq
      rw [add_mul, polynomialGaussian_add]
      exact (meanZeroGaussianSquareSpan m).add_mem (h₁ q hq) (h₂ q hq)
    | mul p₁ p₂ _ _ h₁ h₂ =>
      intro q hq
      rw [mul_assoc]
      exact h₁ _ (h₂ q hq)
  simpa only [mul_one] using hstable p hp 1 (polynomialGaussian_one_mem_squareSpan m)

end
end GaussianTesting
