module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SymplecticAction
public import GaussianTesting.Bosons.SchrodingerVacuum
public import GaussianTesting.Bosons.CharacteristicInjectivity
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# Centered Gaussian wavefunctions are symplectic vacuum states

A normalized exponential of a homogeneous complex quadratic form with strictly
negative real part is a symplectic Gaussian unitary applied to the vacuum, up
to a scalar of unit modulus. The construction uses the positive square root of
the real quadratic form and the quadratic phase given by its imaginary part.
-/

namespace GaussianTesting

open MeasureTheory Matrix
open scoped InnerProductSpace MatrixOrder

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true

/-- Normalized vectors with the same characteristic function differ by a unit scalar. -/
theorem exists_unit_smul_of_pureWaveCharacteristic_eq {m : ℕ}
    (f g : WaveSpace m) (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (h : pureWaveCharacteristic m f = pureWaveCharacteristic m g) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ f = z • g := by
  have he := congrArg (fun A : WaveSpace m →L[ℂ] WaveSpace m => A f)
    (rankOne_eq_of_pureWaveCharacteristic_eq f g h)
  simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hf] at he
  refine ⟨inner ℂ g f, ?_, he⟩
  have hn := congrArg norm he
  simpa only [hf, norm_smul, hg, mul_one] using hn.symm

/-- Any physical implementation of `S` agrees on rays with the chosen `U_S`.
The proof uses characteristic-function injectivity, so no projective-group
representation theorem is needed. -/
theorem exists_unit_smul_waveSymplecticUnitary {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ symplecticGroup (Fin m) ℝ)
    (U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m)
    (hU : WeylIntertwines U (phaseMatrixAction S))
    (f : WaveSpace m) (hf : ‖f‖ = 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ U f = z • waveSymplecticUnitary S hS f := by
  apply exists_unit_smul_of_pureWaveCharacteristic_eq
    (U f) (waveSymplecticUnitary S hS f)
    ((U.norm_map f).trans hf) (((waveSymplecticUnitary S hS).norm_map f).trans hf)
  funext r
  have hunit : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr
    (SymplecticGroup.symplectic_det hS)
  let : Invertible S := hunit.invertible
  have hp : phaseMatrixAction S (phaseMatrixAction S⁻¹ r) = r := by
    rw [← phaseMatrixAction_mul, Matrix.mul_inv_of_invertible, phaseMatrixAction_one]
  have hw := hU (phaseMatrixAction S⁻¹ r) f
  rw [hp] at hw
  unfold pureWaveCharacteristic
  rw [← hw, U.inner_map_map]
  exact (pureWaveCharacteristic_symplectic S hS r f).symm

private def waveQuadraticMatrix {m : ℕ} (Q : QuadraticForm ℝ (WaveConfig m)) :
    Matrix (Fin m) (Fin m) ℝ :=
  QuadraticForm.toMatrix'
    (Q.comp (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap)

private theorem waveQuadraticMatrix_eval {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m)) (x : WaveConfig m) :
    inner ℝ x (waveMatrixCLM (waveQuadraticMatrix Q) x) = Q x := by
  let Q' : QuadraticForm ℝ (Fin m → ℝ) := Q.comp (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap
  have h := congrArg (fun B : LinearMap.BilinForm ℝ (Fin m → ℝ) => B x x)
    ((LinearMap.toMatrix₂' ℝ).symm_apply_apply Q'.associated)
  change Matrix.toLinearMap₂' ℝ Q'.toMatrix' x x = Q'.associated x x at h
  rw [Matrix.toLinearMap₂'_apply', QuadraticMap.associated_eq_self_apply] at h
  change x.ofLp ⬝ᵥ (Q'.toMatrix' *ᵥ x.ofLp) = Q x at h
  change inner ℝ x (waveMatrixCLM Q'.toMatrix' x) = Q x
  rw [waveMatrixCLM_apply, PiLp.inner_apply]
  simpa only [dotProduct, RCLike.inner_apply, conj_trivial, mul_comm] using h

private theorem waveQuadraticMatrix_symm {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m)) : (waveQuadraticMatrix Q).IsSymm :=
  QuadraticForm.isSymm_toMatrix' _

private theorem waveQuadraticMatrix_posDef {m : ℕ}
    (Q : QuadraticForm ℝ (WaveConfig m)) (hQ : Q.PosDef) :
    (waveQuadraticMatrix Q).PosDef := by
  unfold waveQuadraticMatrix
  apply QuadraticForm.posDef_toMatrix'
  intro x hx
  apply hQ
  intro h
  apply hx
  exact (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.injective h

private theorem waveMatrixCLM_mul_apply {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) (x : WaveConfig m) :
    waveMatrixCLM (A*B) x = waveMatrixCLM A (waveMatrixCLM B x) := by
  simp only [waveMatrixCLM_apply, mulVec_mulVec]

private theorem waveMatrixCLM_one_apply {m : ℕ} (x : WaveConfig m) :
    waveMatrixCLM 1 x = x := by ext i; simp

private theorem waveMatrixCLM_zero_apply {m : ℕ} (x : WaveConfig m) :
    waveMatrixCLM 0 x = 0 := by ext i; simp

private theorem linearChange_intertwines_inverse_matrix {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : IsUnit A) :
    WeylIntertwines (waveLinearChange m (waveMatrixEquiv A hA))
      (phaseMatrixAction (fromBlocks A⁻¹ 0 0 Aᵀ)) := by
  have he : (waveMatrixEquiv A hA).toContinuousLinearMap = waveMatrixCLM A := by
    ext1 x
    exact waveMatrixEquiv_apply A hA x
  have hw := weylIntertwines_linearChange_symm m (waveMatrixEquiv A hA).symm
  intro r f
  simpa only [waveLinearChange, linearCoordinateChange_symm,
    ContinuousLinearEquiv.symm_symm, waveLinearChangePhase,
    phaseMatrixAction_fromBlocks, waveMatrixCLM_zero_apply, add_zero, zero_add,
    waveMatrixEquiv_symm_apply, waveMatrixCLM_transpose, he] using hw r f

private theorem inverse_diagonal_mem_symplectic {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : IsUnit A) :
    fromBlocks A⁻¹ 0 0 Aᵀ ∈ symplecticGroup (Fin m) ℝ := by
  let : Invertible A := hA.invertible
  apply SymplecticGroup.fromBlocks_mem_iff.mpr
  simp only [transpose_zero, mul_zero, zero_mul, sub_zero, true_and,
    transpose_nonsing_inv]
  exact inv_mul_of_invertible Aᵀ

private theorem lowerShear_mem_symplectic {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsSymm) :
    fromBlocks 1 0 A 1 ∈ symplecticGroup (Fin m) ℝ := by
  apply SymplecticGroup.fromBlocks_mem_iff.mpr
  simp [hA.eq]

private theorem sqrt_matrix_norm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.PosDef) (x : WaveConfig m) :
    ‖waveMatrixCLM (CFC.sqrt A) x‖ ^ 2 = inner ℝ x (waveMatrixCLM A x) := by
  have hs : (CFC.sqrt A).IsSymm := by
    change (CFC.sqrt A)ᵀ = CFC.sqrt A
    have h := (CFC.sqrt_nonneg A).posSemidef.isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right,
    ← waveMatrixCLM_transpose, hs.eq, ← waveMatrixCLM_mul_apply,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

/-- Every normalized centered Gaussian wavefunction is a symplectic vacuum
state, including its arbitrary global phase. The real exponent is required
to be strictly negative away from the origin. -/
theorem exists_symplectic_vacuum_of_quadratic_wavefunction {m : ℕ}
    (Q : QuadraticMap ℝ (WaveConfig m) ℂ)
    (hQ : (-Complex.reCLM.toLinearMap.compQuadraticMap Q).PosDef)
    (f : WaveSpace m) (hf : ‖f‖ = 1) (c : ℂ)
    (hfun : (f : WaveConfig m → ℂ) =ᵐ[volume] fun x => c * Complex.exp (Q x)) :
    ∃ (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
      (hS : S ∈ symplecticGroup (Fin m) ℝ) (z : ℂ),
      ‖z‖ = 1 ∧ f = z • waveSymplecticUnitary S hS (waveVacuum m) := by
  let Qr : QuadraticForm ℝ (WaveConfig m) :=
    (2 : ℝ) • (-Complex.reCLM.toLinearMap.compQuadraticMap Q)
  let Qi : QuadraticForm ℝ (WaveConfig m) :=
    (2 : ℝ) • Complex.imCLM.toLinearMap.compQuadraticMap Q
  let A := waveQuadraticMatrix Qr
  let B := waveQuadraticMatrix Qi
  have hA : A.PosDef := waveQuadraticMatrix_posDef Qr (hQ.smul (a := (2 : ℝ)) (by norm_num))
  have hB : B.IsSymm := waveQuadraticMatrix_symm Qi
  let C := CFC.sqrt A
  have hC : IsUnit C := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  let E := waveMatrixEquiv C hC
  let U := (waveLinearChange m E).trans (waveQuadraticPhase m (waveMatrixCLM B))
  let S := fromBlocks 1 0 B 1 * fromBlocks C⁻¹ 0 0 Cᵀ
  have hS : S ∈ symplecticGroup (Fin m) ℝ :=
    (symplecticGroup (Fin m) ℝ).mul_mem (lowerShear_mem_symplectic B hB)
      (inverse_diagonal_mem_symplectic C hC)
  have hU : WeylIntertwines U (phaseMatrixAction S) := by
    have hh := (linearChange_intertwines_inverse_matrix C hC).trans
      (weylIntertwines_quadraticPhase m (waveMatrixCLM B) (waveMatrixCLM_symmetric hB))
    intro r v
    simpa only [Function.comp_apply, S, phaseMatrixAction_mul,
      phaseMatrixAction_fromBlocks, waveMatrixCLM_one_apply, waveMatrixCLM_zero_apply,
      add_zero, zero_add, add_comm] using hh r v
  have hnorm (x : WaveConfig m) : ‖E x‖ ^ 2 = -2 * (Q x).re := by
    rw [waveMatrixEquiv_apply, sqrt_matrix_norm A hA, waveQuadraticMatrix_eval]
    change 2 * (-(Q x).re) = _
    ring
  have himag (x : WaveConfig m) : inner ℝ x (waveMatrixCLM B x) = 2 * (Q x).im := by
    exact waveQuadraticMatrix_eval Qi x
  have hquad (x : WaveConfig m) :
      Complex.I * ((inner ℝ x (waveMatrixCLM B x) / 2 : ℝ) : ℂ) +
        ((-‖E x‖ ^ 2 / 2 : ℝ) : ℂ) = Q x := by
    rw [hnorm, himag]
    apply Complex.ext <;> simp
  let k : ℂ := ((waveLinearChangeScale E * Real.pi ^ (-(m : ℝ) / 4) : ℝ) : ℂ)
  have hk : k ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (mul_pos (linearCoordinateChangeScale_pos E)
      (Real.rpow_pos_of_pos Real.pi_pos _))
  have hUfun : (U (waveVacuum m) : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => k * Complex.exp (Q x) := by
    filter_upwards [waveQuadraticPhase_coeFn m (waveMatrixCLM B)
        (waveLinearChange m E (waveVacuum m)),
      waveLinearChange_coeFn m E (waveVacuum m),
      (waveLinearChange_quasiMeasurePreserving E).ae_eq_comp (waveVacuum_coeFn m)]
      with x hx hy hz
    change waveQuadraticPhase m (waveMatrixCLM B)
      (waveLinearChange m E (waveVacuum m)) x = _
    simp only [Function.comp_apply] at hz
    rw [hx, hy, hz]
    simp only [waveVacuumFun, Complex.ofReal_exp]
    rw [← hquad x, Complex.exp_add]
    simp only [k, Complex.ofReal_mul]
    ring
  have hfU : f = (c/k) • U (waveVacuum m) := by
    apply Lp.ext
    filter_upwards [hfun, hUfun, Lp.coeFn_smul (c/k) (U (waveVacuum m))] with x hx hy hz
    rw [hx, hz]
    change _ = (c/k) * U (waveVacuum m) x
    rw [hy, ← mul_assoc, div_mul_cancel₀ c hk]
  have hc : ‖c/k‖ = 1 := by
    have hn := congrArg norm hfU
    simpa only [hf, norm_smul, U.norm_map, waveVacuum_norm, mul_one] using hn.symm
  obtain ⟨z, hz, he⟩ := exists_unit_smul_waveSymplecticUnitary S hS U hU
    (waveVacuum m) (waveVacuum_norm m)
  refine ⟨S, hS, (c/k)*z, ?_, ?_⟩
  · rw [norm_mul, hc, hz, one_mul]
  · rw [hfU, he, smul_smul]

end
end GaussianTesting
