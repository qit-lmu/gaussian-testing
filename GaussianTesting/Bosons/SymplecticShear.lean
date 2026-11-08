module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.WeylRotation

@[expose] public section

/-!
# Symplectic shears on Schrödinger wavefunctions

A real symmetric quadratic form gives the unitary phase multiplier
`C_A f(x) = exp(i ⟪x, A x⟫ / 2) f(x)`. Its conjugation of Weyl operators
implements the symplectic shear `(q,p) ↦ (q,p-Aq)`. Applying the same phase
multiplier to both copies commutes with their coordinate rotation.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

/-- The quadratic scalar phase associated with a real linear map. -/
def waveQuadraticForm (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m) :
    C(WaveConfig m, ℝ) := ⟨fun x => inner ℝ x (A x) / 2, by fun_prop⟩

/-- The unitary quadratic phase multiplier; symmetry is required for its
identification with a prescribed symplectic shear, not for unitarity. -/
def waveQuadraticPhase (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m) :
    WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m := wavePhaseMultiplier (waveQuadraticForm m A)

theorem waveQuadraticPhase_coeFn (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m)
    (f : WaveSpace m) :
    (waveQuadraticPhase m A f : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => Complex.exp (Complex.I * ((inner ℝ x (A x) / 2 : ℝ) : ℂ)) * f x :=
  wavePhaseMultiplier_coeFn _ f

/-- The inverse quadratic phase negates the real quadratic form. -/
theorem waveQuadraticPhase_symm (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m) :
    (waveQuadraticPhase m A).symm = waveQuadraticPhase m (-A) := by
  have h (f : WaveSpace m) : waveQuadraticPhase m A (waveQuadraticPhase m (-A) f) = f := by
    apply Lp.ext
    filter_upwards [waveQuadraticPhase_coeFn m A (waveQuadraticPhase m (-A) f),
      waveQuadraticPhase_coeFn m (-A) f] with x hx hy
    rw [hx, hy, ← mul_assoc, ← Complex.exp_add]
    simp
    ring_nf
    simp
  ext f : 1
  apply (waveQuadraticPhase m A).injective
  rw [LinearIsometryEquiv.apply_symm_apply, h]

private theorem quadraticPhase_weyl_phase {m : ℕ}
    (A : WaveConfig m →L[ℝ] WaveConfig m) (hA : A.toLinearMap.IsSymmetric)
    (r : WavePhase m) (x : WaveConfig m) :
    Complex.exp (Complex.I * ((inner ℝ x (A x) / 2 : ℝ) : ℂ)) *
        weylPhase (r.1, r.2 - A r.1) x =
      weylPhase r x *
        Complex.exp (Complex.I * ((inner ℝ (x-r.1) (A (x-r.1)) / 2 : ℝ) : ℂ)) := by
  simp only [weylPhase, ← Complex.exp_add]
  congr 1
  rw [← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 2
  simp only [map_sub, inner_sub_left, inner_sub_right]
  have h := hA x r.1
  have h' := real_inner_comm (A x) r.1
  have h'' := real_inner_comm (A r.1) x
  have h₀ := real_inner_comm (A r.1) r.1
  dsimp at h
  linarith

/-- A symmetric quadratic phase implements the inverse symplectic shear on
Weyl parameters, with the manuscript's conjugation convention. -/
theorem waveQuadraticPhase_weyl (m : ℕ)
    (A : WaveConfig m →L[ℝ] WaveConfig m) (hA : A.toLinearMap.IsSymmetric)
    (r : WavePhase m) (f : WaveSpace m) :
    (waveQuadraticPhase m A).symm (weylOperator m r (waveQuadraticPhase m A f)) =
      weylOperator m (r.1, r.2 - A r.1) f := by
  apply (waveQuadraticPhase m A).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [weylOperator_coeFn m r (waveQuadraticPhase m A f),
    (waveTranslation_measurePreserving r.1).quasiMeasurePreserving.ae_eq_comp
      (waveQuadraticPhase_coeFn m A f),
    waveQuadraticPhase_coeFn m A (weylOperator m (r.1, r.2 - A r.1) f),
    weylOperator_coeFn m (r.1, r.2 - A r.1) f] with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃, h₄, ← mul_assoc, ← mul_assoc, quadraticPhase_weyl_phase A hA]

/-- The shear preserves the manuscript's symplectic form. -/
theorem waveQuadraticPhase_symplectic (m : ℕ)
    (A : WaveConfig m →L[ℝ] WaveConfig m) (hA : A.toLinearMap.IsSymmetric)
    (r s : WavePhase m) :
    waveSymplectic (r.1, r.2 - A r.1) (s.1, s.2 - A s.1) =
      waveSymplectic r s := by
  simp only [waveSymplectic, inner_sub_left, inner_sub_right]
  have h := hA r.1 s.1
  dsimp at h
  linarith


private theorem pairPhaseMul_memLp {m : ℕ} (a : C(BosonConfig m, ℝ)) (f : SchrodingerSpace m) :
    MemLp (fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x) 2 volume := by
  apply (Lp.memLp f).congr_norm
  · exact ((Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp a.continuous))).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_exp_I_mul_ofReal]

/-- Multiplication of two-copy wavefunctions by a continuous scalar phase. -/
def pairPhaseMul {m : ℕ} (a : C(BosonConfig m, ℝ)) (f : SchrodingerSpace m) : SchrodingerSpace m :=
  ((by exact pairPhaseMul_memLp a f) :
    MemLp (fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x) 2 volume).toLp _

private theorem pairPhaseMul_coeFn {m : ℕ} (a : C(BosonConfig m, ℝ)) (f : SchrodingerSpace m) :
    (pairPhaseMul a f : BosonConfig m → ℂ) =ᵐ[volume]
      fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x :=
  (pairPhaseMul_memLp a f).coeFn_toLp

/-- Two-copy scalar-phase multiplication bundled as a complex linear map. -/
def pairPhaseMulLinear {m : ℕ} (a : C(BosonConfig m, ℝ)) :
    SchrodingerSpace m →ₗ[ℂ] SchrodingerSpace m where
  toFun := pairPhaseMul a
  map_add' f g := by
    apply Lp.ext
    filter_upwards [pairPhaseMul_coeFn a (f+g), pairPhaseMul_coeFn a f, pairPhaseMul_coeFn a g,
      Lp.coeFn_add f g, Lp.coeFn_add (pairPhaseMul a f) (pairPhaseMul a g)] with x h h₁ h₂ h₃ h₄
    simp only [h, h₄, h₁, h₂, h₃, Pi.add_apply, mul_add]
  map_smul' c f := by
    change pairPhaseMul a (c • f) = c • pairPhaseMul a f
    apply Lp.ext
    filter_upwards [pairPhaseMul_coeFn a (c • f), pairPhaseMul_coeFn a f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (pairPhaseMul a f)] with x h h₁ h₂ h₃
    simp only [h, h₃, h₁, h₂, Pi.smul_apply, smul_eq_mul, mul_left_comm]

private theorem pairPhaseMul_norm {m : ℕ} (a : C(BosonConfig m, ℝ)) (f : SchrodingerSpace m) :
    ‖pairPhaseMul a f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [pairPhaseMul_coeFn a f] with x hx
  rw [hx, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

private theorem pairPhaseMul_neg {m : ℕ} (a : C(BosonConfig m, ℝ)) (f : SchrodingerSpace m) :
    pairPhaseMul (-a) (pairPhaseMul a f) = f := by
  apply Lp.ext
  filter_upwards [pairPhaseMul_coeFn (-a) (pairPhaseMul a f), pairPhaseMul_coeFn a f] with x hx hy
  rw [hx, hy, ← mul_assoc, ← Complex.exp_add]
  simp

/-- Multiplication by a continuous scalar phase is unitary on wavefunctions. -/
def schrodingerPhaseMultiplier {m : ℕ} (a : C(BosonConfig m, ℝ)) :
    SchrodingerSpace m ≃ₗᵢ[ℂ] SchrodingerSpace m :=
  LinearIsometryEquiv.ofLinearIsometry
    { pairPhaseMulLinear a with norm_map' := by exact pairPhaseMul_norm a }
    (pairPhaseMulLinear (-a))
    (by
      ext f : 1
      change pairPhaseMul a (pairPhaseMul (-a) f) = f
      simpa only [neg_neg] using pairPhaseMul_neg (-a) f)
    (by
      ext f : 1
      change pairPhaseMul (-a) (pairPhaseMul a f) = f
      exact pairPhaseMul_neg a f)

theorem schrodingerPhaseMultiplier_coeFn {m : ℕ} (a : C(BosonConfig m, ℝ)) (f : SchrodingerSpace m) :
    (schrodingerPhaseMultiplier a f : BosonConfig m → ℂ) =ᵐ[volume]
      fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x := pairPhaseMul_coeFn a f


attribute [local irreducible] waveQuadraticPhase schrodingerPhaseMultiplier

/-- The sum of the identical quadratic forms on the two copies. -/
def twoCopyQuadraticForm (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m) :
    C(BosonConfig m, ℝ) :=
  ⟨fun z => inner ℝ (bosonPosition 0 z) (A (bosonPosition 0 z)) / 2 +
      inner ℝ (bosonPosition 1 z) (A (bosonPosition 1 z)) / 2, by
    have hc (i : Fin 2) : Continuous (bosonPosition (m := m) i) := by
      unfold bosonPosition
      apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
      fun_prop
    exact ((hc 0).inner (𝕜 := ℝ) (A.continuous.comp (hc 0))).div_const 2 |>.add
      (((hc 1).inner (𝕜 := ℝ) (A.continuous.comp (hc 1))).div_const 2)⟩

/-- Rotation invariance of the sum of two identical quadratic forms. -/
theorem twoCopyQuadraticForm_rotate (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m)
    (θ : ℝ) (z : BosonConfig m) :
    twoCopyQuadraticForm m A (bosonRotate θ z) = twoCopyQuadraticForm m A z := by
  dsimp [twoCopyQuadraticForm]
  rw [bosonPosition_rotate_zero, bosonPosition_rotate_one]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right]
  linear_combination ((inner ℝ (bosonPosition 0 z) (A (bosonPosition 0 z)) +
      inner ℝ (bosonPosition 1 z) (A (bosonPosition 1 z))) / 2) *
    Real.sin_sq_add_cos_sq θ

/-- An invariant scalar phase commutes with the coordinate rotation on L². -/
theorem schrodingerRotation_phaseMultiplier (m : ℕ) (θ : ℝ)
    (a : C(BosonConfig m, ℝ)) (ha : ∀ z, a (bosonRotate θ z) = a z)
    (f : SchrodingerSpace m) :
    schrodingerRotation m θ (schrodingerPhaseMultiplier a f) =
      schrodingerPhaseMultiplier a (schrodingerRotation m θ f) := by
  apply Lp.ext
  filter_upwards [schrodingerRotation_coeFn m θ (schrodingerPhaseMultiplier a f),
    (bosonRotation_measurePreserving m θ).quasiMeasurePreserving.ae_eq_comp
      (schrodingerPhaseMultiplier_coeFn a f),
    schrodingerPhaseMultiplier_coeFn a (schrodingerRotation m θ f),
    schrodingerRotation_coeFn m θ f] with z h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃, h₄, ha]

/-- Identical one-copy quadratic phase multipliers act by their sum on the
actual two-copy wavefunction. -/
theorem waveTensor_quadraticPhase (m : ℕ) (A : WaveConfig m →L[ℝ] WaveConfig m)
    (v : HilbertSquare (WaveSpace m)) :
    waveTensor m (hilbertTensorMap
      (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap
      (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap v) =
    schrodingerPhaseMultiplier (twoCopyQuadraticForm m A) (waveTensor m v) := by
  have h : (waveTensor m).toContinuousLinearMap.comp (hilbertTensorMap
      (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap
      (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap) =
      (schrodingerPhaseMultiplier (twoCopyQuadraticForm m A)).toLinearIsometry.toContinuousLinearMap.comp
        (waveTensor m).toContinuousLinearMap := by
    apply hilbertTensor_ext
    intro f g
    simp only [ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    apply Lp.ext
    have h0 : QuasiMeasurePreserving (bosonPosition (m := m) 0) volume volume :=
      quasiMeasurePreserving_fst.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
    have h1 : QuasiMeasurePreserving (bosonPosition (m := m) 1) volume volume :=
      quasiMeasurePreserving_snd.comp (bosonPositions_measurePreserving m).quasiMeasurePreserving
    filter_upwards [waveTensor_tmul_coeFn m (waveQuadraticPhase m A f) (waveQuadraticPhase m A g),
      h0.ae_eq_comp (waveQuadraticPhase_coeFn m A f),
      h1.ae_eq_comp (waveQuadraticPhase_coeFn m A g),
      schrodingerPhaseMultiplier_coeFn (twoCopyQuadraticForm m A) (waveTensor m (hilbertTmul f g)),
      waveTensor_tmul_coeFn m f g] with z hT hf hg hP hT'
    simp only [Function.comp_apply] at hf hg
    have hleft := hT.trans (congrArg₂ (fun a b : ℂ => a * b) hf hg)
    have hright := hP.trans (congrArg
      (fun a : ℂ => Complex.exp (Complex.I *
        (twoCopyQuadraticForm m A z : ℂ)) * a) hT')
    apply hleft.trans
    apply Eq.trans _ hright.symm
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    dsimp [twoCopyQuadraticForm]
    push_cast
    ring
  exact congrArg (fun B => B v) h

/-- The same quadratic phase applied to both copies commutes with every
copy rotation, as required for symplectic Gaussian actions in Section 6. -/
theorem schrodingerTensorRotation_quadraticPhase (m : ℕ)
    (A : WaveConfig m →L[ℝ] WaveConfig m) (θ : ℝ)
    (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorRotation m θ (hilbertTensorMap
      (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap
      (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap v) =
    hilbertTensorMap (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap
      (waveQuadraticPhase m A).toLinearIsometry.toContinuousLinearMap
      (schrodingerTensorRotation m θ v) := by
  apply (waveTensorEquiv m).injective
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, waveTensorEquiv_apply]
  rw [waveTensor_quadraticPhase, waveTensor_quadraticPhase]
  simp only [← waveTensorEquiv_apply, LinearIsometryEquiv.apply_symm_apply]
  exact schrodingerRotation_phaseMultiplier m θ _ (twoCopyQuadraticForm_rotate m A θ) _

end
end GaussianTesting
