module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerTensor
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

/-!
# Weyl displacements on Schrödinger wavefunctions

The explicit action in Section 6 is the definition:
`D_(x,p) f(z) = exp(i (⟪p,z⟫ - ⟪p,x⟫ / 2)) f(z-x)`.
The local translation parameter `q` below denotes the manuscript position
displacement `x`; `WavePhase` stores the position and momentum in that order.
Translation preserves Lebesgue measure and the multiplier has modulus one,
so this defines a unitary on all of the actual `L²` space. No unbounded
operator exponential is used in the construction.
-/

namespace GaussianTesting

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Position and momentum displacement parameters, in that order. -/
abbrev WavePhase (m : ℕ) := WaveConfig m × WaveConfig m

/-- The standard symplectic form `rᵀ Ω s` for `r=(q,p)`. -/
def waveSymplectic {m : ℕ} (r s : WavePhase m) : ℝ :=
  inner ℝ r.1 s.2 - inner ℝ r.2 s.1

/-- The pointwise scalar multiplier in the explicit Weyl action. -/
def weylPhase {m : ℕ} (r : WavePhase m) (x : WaveConfig m) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ r.2 x - inner ℝ r.2 r.1 / 2 : ℝ) : ℂ))

@[simp] theorem weylPhase_norm {m : ℕ} (r : WavePhase m) (x : WaveConfig m) :
    ‖weylPhase r x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

theorem continuous_weylPhase (m : ℕ) :
    Continuous (fun z : WavePhase m × WaveConfig m => weylPhase z.1 z.2) := by
  unfold weylPhase
  fun_prop

/-- Translation of positions preserves Lebesgue measure. -/
theorem waveTranslation_measurePreserving {m : ℕ} (q : WaveConfig m) :
    MeasurePreserving (fun x : WaveConfig m => x - q) := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure (WaveConfig m)) (-q)

/-- The unitary translation `f(x) ↦ f(x-q)`. -/
def waveTranslation (m : ℕ) (q : WaveConfig m) : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m := by
  let T : WaveSpace m →ₗᵢ[ℂ] WaveSpace m := Lp.compMeasurePreservingₗᵢ ℂ (fun x : WaveConfig m => x - q)
    (waveTranslation_measurePreserving q)
  let R : WaveSpace m →ₗ[ℂ] WaveSpace m := Lp.compMeasurePreservingₗ ℂ (fun x : WaveConfig m => x - (-q))
    (waveTranslation_measurePreserving (-q))
  refine LinearIsometryEquiv.ofLinearIsometry T R ?_ ?_
  · ext f : 1
    change Lp.compMeasurePreserving (fun x : WaveConfig m => x - q)
      (waveTranslation_measurePreserving q) (R f) = f
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (R f) (waveTranslation_measurePreserving q),
      (waveTranslation_measurePreserving q).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_compMeasurePreserving f (waveTranslation_measurePreserving (-q)))] with x hx hy
    simpa only [Function.comp_apply, sub_neg_eq_add, sub_add_cancel] using hx.trans hy
  · ext f : 1
    change Lp.compMeasurePreserving (fun x : WaveConfig m => x - (-q))
      (waveTranslation_measurePreserving (-q)) (T f) = f
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (T f) (waveTranslation_measurePreserving (-q)),
      (waveTranslation_measurePreserving (-q)).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_compMeasurePreserving f (waveTranslation_measurePreserving q))] with x hx hy
    simpa only [Function.comp_apply, sub_neg_eq_add, add_sub_cancel_right] using hx.trans hy

theorem waveTranslation_coeFn (m : ℕ) (q : WaveConfig m) (f : WaveSpace m) :
    (waveTranslation m q f : WaveConfig m → ℂ) =ᵐ[volume] fun x => f (x-q) :=
  Lp.coeFn_compMeasurePreserving f (waveTranslation_measurePreserving q)

private theorem phaseMul_memLp {m : ℕ} (a : C(WaveConfig m, ℝ)) (f : WaveSpace m) :
    MemLp (fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x) 2 volume := by
  apply (Lp.memLp f).congr_norm
  · exact ((Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp a.continuous))).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_exp_I_mul_ofReal]

/-- Multiplication of wavefunctions by a continuous scalar phase. -/
def phaseMul {m : ℕ} (a : C(WaveConfig m, ℝ)) (f : WaveSpace m) : WaveSpace m :=
  ((by exact phaseMul_memLp a f) :
    MemLp (fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x) 2 volume).toLp _

private theorem phaseMul_coeFn {m : ℕ} (a : C(WaveConfig m, ℝ)) (f : WaveSpace m) :
    (phaseMul a f : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x :=
  (phaseMul_memLp a f).coeFn_toLp

/-- Scalar-phase multiplication bundled as a complex linear map. -/
def phaseMulLinear {m : ℕ} (a : C(WaveConfig m, ℝ)) :
    WaveSpace m →ₗ[ℂ] WaveSpace m where
  toFun := phaseMul a
  map_add' f g := by
    apply Lp.ext
    filter_upwards [phaseMul_coeFn a (f+g), phaseMul_coeFn a f, phaseMul_coeFn a g,
      Lp.coeFn_add f g, Lp.coeFn_add (phaseMul a f) (phaseMul a g)] with x h h₁ h₂ h₃ h₄
    simp only [h, h₄, h₁, h₂, h₃, Pi.add_apply, mul_add]
  map_smul' c f := by
    change phaseMul a (c • f) = c • phaseMul a f
    apply Lp.ext
    filter_upwards [phaseMul_coeFn a (c • f), phaseMul_coeFn a f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (phaseMul a f)] with x h h₁ h₂ h₃
    simp only [h, h₃, h₁, h₂, Pi.smul_apply, smul_eq_mul, mul_left_comm]

private theorem phaseMul_norm {m : ℕ} (a : C(WaveConfig m, ℝ)) (f : WaveSpace m) :
    ‖phaseMul a f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [phaseMul_coeFn a f] with x hx
  rw [hx, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

private theorem phaseMul_neg {m : ℕ} (a : C(WaveConfig m, ℝ)) (f : WaveSpace m) :
    phaseMul (-a) (phaseMul a f) = f := by
  apply Lp.ext
  filter_upwards [phaseMul_coeFn (-a) (phaseMul a f), phaseMul_coeFn a f] with x hx hy
  rw [hx, hy, ← mul_assoc, ← Complex.exp_add]
  simp

/-- Multiplication by a continuous scalar phase is unitary on wavefunctions. -/
def wavePhaseMultiplier {m : ℕ} (a : C(WaveConfig m, ℝ)) :
    WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m :=
  LinearIsometryEquiv.ofLinearIsometry
    { phaseMulLinear a with norm_map' := by exact phaseMul_norm a }
    (phaseMulLinear (-a))
    (by
      ext f : 1
      change phaseMul a (phaseMul (-a) f) = f
      simpa only [neg_neg] using phaseMul_neg (-a) f)
    (by
      ext f : 1
      change phaseMul (-a) (phaseMul a f) = f
      exact phaseMul_neg a f)

theorem wavePhaseMultiplier_coeFn {m : ℕ} (a : C(WaveConfig m, ℝ)) (f : WaveSpace m) :
    (wavePhaseMultiplier a f : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => Complex.exp (Complex.I * (a x : ℂ)) * f x := phaseMul_coeFn a f

/-- The unitary modulation `f(x) ↦ exp(i⟪p,x⟫) f(x)`. -/
def waveModulation (m : ℕ) (p : WaveConfig m) : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m :=
  wavePhaseMultiplier ⟨fun x => inner ℝ p x, by fun_prop⟩

theorem waveModulation_coeFn (m : ℕ) (p : WaveConfig m) (f : WaveSpace m) :
    (waveModulation m p f : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * f x :=
  wavePhaseMultiplier_coeFn _ f

/-- The Weyl operator, defined by the explicit Schrödinger action. -/
def weylOperator (m : ℕ) (r : WavePhase m) : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m :=
  (waveTranslation m r.1).trans
    (wavePhaseMultiplier ⟨fun x => inner ℝ r.2 x - inner ℝ r.2 r.1 / 2, by fun_prop⟩)

/-- The defining formula is an equality of representatives almost everywhere. -/
theorem weylOperator_coeFn (m : ℕ) (r : WavePhase m) (f : WaveSpace m) :
    (weylOperator m r f : WaveConfig m → ℂ) =ᵐ[volume]
      fun x => weylPhase r x * f (x-r.1) := by
  filter_upwards [wavePhaseMultiplier_coeFn
      ⟨fun x => inner ℝ r.2 x - inner ℝ r.2 r.1 / 2, by fun_prop⟩
      (waveTranslation m r.1 f), waveTranslation_coeFn m r.1 f] with x hx hy
  exact hx.trans (congrArg (fun z => weylPhase r x * z) hy)


/-- The scalar phase, modulation, and translation factorization. -/
theorem weylOperator_factorization (m : ℕ) (r : WavePhase m) (f : WaveSpace m) :
    weylOperator m r f =
      Complex.exp (-Complex.I * (inner ℝ r.2 r.1 : ℂ) / 2) •
        waveModulation m r.2 (waveTranslation m r.1 f) := by
  apply Lp.ext
  filter_upwards [weylOperator_coeFn m r f,
    waveModulation_coeFn m r.2 (waveTranslation m r.1 f),
    waveTranslation_coeFn m r.1 f,
    Lp.coeFn_smul (Complex.exp (-Complex.I * (inner ℝ r.2 r.1 : ℂ) / 2))
      (waveModulation m r.2 (waveTranslation m r.1 f))] with x h₁ h₂ h₃ h₄
  rw [h₁, h₄]
  simp only [Pi.smul_apply, smul_eq_mul, h₂, h₃]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  unfold weylPhase
  congr 1
  push_cast
  ring

@[simp] theorem weylOperator_zero (m : ℕ) (f : WaveSpace m) :
    weylOperator m 0 f = f := by
  apply Lp.ext
  filter_upwards [weylOperator_coeFn m 0 f] with x hx
  simpa [weylPhase] using hx

/-- Pointwise phase identity fixing the sign of the Weyl composition law. -/
theorem weylPhase_mul {m : ℕ} (r s : WavePhase m) (x : WaveConfig m) :
    weylPhase r x * weylPhase s (x-r.1) =
      Complex.exp (-Complex.I * (waveSymplectic r s : ℂ) / 2) * weylPhase (r+s) x := by
  simp only [weylPhase, waveSymplectic, ← Complex.exp_add,
    Prod.fst_add, Prod.snd_add, inner_sub_right, inner_add_left, inner_add_right]
  congr 1
  rw [real_inner_comm s.2 r.1]
  push_cast
  ring

/-- The Weyl composition law with the manuscript's symplectic sign. -/
theorem weylOperator_mul (m : ℕ) (r s : WavePhase m) (f : WaveSpace m) :
    weylOperator m r (weylOperator m s f) =
      Complex.exp (-Complex.I * (waveSymplectic r s : ℂ) / 2) • weylOperator m (r+s) f := by
  apply Lp.ext
  filter_upwards [weylOperator_coeFn m r (weylOperator m s f),
    (waveTranslation_measurePreserving r.1).quasiMeasurePreserving.ae_eq_comp
      (weylOperator_coeFn m s f), weylOperator_coeFn m (r+s) f,
    Lp.coeFn_smul (Complex.exp (-Complex.I * (waveSymplectic r s : ℂ) / 2))
      (weylOperator m (r+s) f)] with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₄]
  simp only [Pi.smul_apply, smul_eq_mul, h₃, Prod.fst_add]
  rw [← mul_assoc, weylPhase_mul, mul_assoc]
  congr 2
  abel_nf

@[simp] theorem waveSymplectic_self {m : ℕ} (r : WavePhase m) :
    waveSymplectic r r = 0 := by
  simp [waveSymplectic, real_inner_comm]

@[simp] theorem waveSymplectic_neg_right {m : ℕ} (r s : WavePhase m) :
    waveSymplectic r (-s) = -waveSymplectic r s := by
  simp only [waveSymplectic, Prod.fst_neg, Prod.snd_neg, inner_neg_right]
  ring

@[simp] theorem waveSymplectic_neg_left {m : ℕ} (r s : WavePhase m) :
    waveSymplectic (-r) s = -waveSymplectic r s := by
  simp only [waveSymplectic, Prod.fst_neg, Prod.snd_neg, inner_neg_left]
  ring

@[simp] theorem weylOperator_neg_right (m : ℕ) (r : WavePhase m) (f : WaveSpace m) :
    weylOperator m r (weylOperator m (-r) f) = f := by
  simpa using weylOperator_mul m r (-r) f

@[simp] theorem weylOperator_neg_left (m : ℕ) (r : WavePhase m) (f : WaveSpace m) :
    weylOperator m (-r) (weylOperator m r f) = f := by
  simpa using weylOperator_mul m (-r) r f

/-- Taking the adjoint unitary negates the displacement parameter. -/
@[simp] theorem weylOperator_symm_neg (m : ℕ) (r : WavePhase m) :
    (weylOperator m r).symm = weylOperator m (-r) := by
  ext f : 1
  apply (weylOperator m r).injective
  rw [LinearIsometryEquiv.apply_symm_apply, weylOperator_neg_right]

/-- The bounded-operator adjoint is the displacement with opposite parameter. -/
theorem weylOperator_adjoint (m : ℕ) (r : WavePhase m) :
    (weylOperator m r).toLinearIsometry.toContinuousLinearMap.adjoint =
      (weylOperator m (-r)).toLinearIsometry.toContinuousLinearMap := by
  exact (weylOperator m r).adjoint_eq_symm.trans
    (congrArg (fun e : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m =>
      e.toLinearIsometry.toContinuousLinearMap) (weylOperator_symm_neg m r))

@[simp] theorem weylOperator_norm (m : ℕ) (r : WavePhase m) (f : WaveSpace m) :
    ‖weylOperator m r f‖ = ‖f‖ := (weylOperator m r).norm_map f

@[simp] theorem weylOperator_inner (m : ℕ) (r : WavePhase m) (f g : WaveSpace m) :
    inner ℂ (weylOperator m r f) (weylOperator m r g) = inner ℂ f g :=
  (weylOperator m r).inner_map_map f g

end
end GaussianTesting
