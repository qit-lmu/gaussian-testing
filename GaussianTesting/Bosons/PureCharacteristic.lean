module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.CharacteristicFunction
public import GaussianTesting.Bosons.PartialTrace

@[expose] public section

/-!
# Pure-state characteristic functions and displacement covariance

The expectation of the explicit Weyl action agrees with the manuscript's
trace definition for the rank-one density operator. Conjugating by a Weyl
displacement gives the scalar character used in Section 6.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

/-- The Weyl expectation of a wavefunction, normalized when the vector is unit. -/
def pureWaveCharacteristic (m : ℕ) (f : WaveSpace m) (r : WavePhase m) : ℂ :=
  inner ℂ f (weylOperator m r f)

/-- Pure-state expectations equal the manuscript's trace definition. -/
theorem waveCharacteristic_rankOne {m : ℕ} {κ : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m)) (f : WaveSpace m) (r : WavePhase m) :
    waveCharacteristic b (InnerProductSpace.rankOne ℂ f f) r =
      pureWaveCharacteristic m f r :=
  HilbertDensity.operatorTrace_rankOne_mul b _ f f

@[simp] theorem pureWaveCharacteristic_zero (m : ℕ) (f : WaveSpace m) :
    pureWaveCharacteristic m f 0 = (‖f‖ ^ 2 : ℝ) := by
  simp [pureWaveCharacteristic, inner_self_eq_norm_sq_to_K]

/-- Continuity holds for all wavefunctions, without moment assumptions. -/
theorem continuous_pureWaveCharacteristic (m : ℕ) (f : WaveSpace m) :
    Continuous (pureWaveCharacteristic m f) :=
  continuous_const.inner (𝕜 := ℂ) (continuous_weylOperator m f)

theorem norm_pureWaveCharacteristic_le (m : ℕ) (f : WaveSpace m) (r : WavePhase m) :
    ‖pureWaveCharacteristic m f r‖ ≤ ‖f‖ ^ 2 := by
  simpa only [pureWaveCharacteristic, weylOperator_norm, pow_two] using
    norm_inner_le_norm f (weylOperator m r f)

theorem pureWaveCharacteristic_neg (m : ℕ) (f : WaveSpace m) (r : WavePhase m) :
    pureWaveCharacteristic m f (-r) = star (pureWaveCharacteristic m f r) := by
  unfold pureWaveCharacteristic
  rw [← (weylOperator m r).inner_map_map f (weylOperator m (-r) f),
    weylOperator_neg_right]
  exact (inner_conj_symm (𝕜 := ℂ) (weylOperator m r f) f).symm

theorem waveSymplectic_swap {m : ℕ} (r s : WavePhase m) :
    waveSymplectic s r = -waveSymplectic r s := by
  unfold waveSymplectic
  rw [real_inner_comm s.1 r.2, real_inner_comm s.2 r.1]
  ring

theorem waveSymplectic_add_right {m : ℕ} (r s t : WavePhase m) :
    waveSymplectic r (s+t) = waveSymplectic r s + waveSymplectic r t := by
  simp only [waveSymplectic, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

/-- Displacement conjugation, with the manuscript's sign convention. -/
theorem weylOperator_conjugate (m : ℕ) (a r : WavePhase m) (f : WaveSpace m) :
    weylOperator m (-a) (weylOperator m r (weylOperator m a f)) =
      Complex.exp (Complex.I * (waveSymplectic a r : ℂ)) • weylOperator m r f := by
  rw [weylOperator_mul m r a f, map_smul, weylOperator_mul, smul_smul,
    ← Complex.exp_add]
  have hp : -a + (r+a) = r := by abel
  rw [hp]
  congr 1
  congr 1
  rw [waveSymplectic_neg_left, waveSymplectic_add_right, waveSymplectic_self,
    add_zero, waveSymplectic_swap r a]
  push_cast
  ring

/-- Translating a state multiplies its characteristic function by a character. -/
theorem pureWaveCharacteristic_displacement (m : ℕ) (a r : WavePhase m)
    (f : WaveSpace m) :
    pureWaveCharacteristic m (weylOperator m a f) r =
      Complex.exp (Complex.I * (waveSymplectic a r : ℂ)) *
        pureWaveCharacteristic m f r := by
  unfold pureWaveCharacteristic
  rw [(weylOperator m a).inner_map_eq_flip, weylOperator_symm_neg,
    weylOperator_conjugate, inner_smul_right]

end
end GaussianTesting
