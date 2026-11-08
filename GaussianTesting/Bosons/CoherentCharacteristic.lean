module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.WeylRotation
public import GaussianTesting.Bosons.VacuumCharacteristic
public import GaussianTesting.Bosons.CoherentCharacteristicEquation
public import GaussianTesting.Bosons.CharacteristicInjectivity

@[expose] public section

/-!
# The characteristic-function argument for coherent certainty

This part of Proposition 6.3 starts with the actual factorization after the
inverse balanced splitter. Weyl covariance gives the characteristic-function
equation. Dividing by the vacuum characteristic function gives a continuous
unit-circle character, and hence the exponential of a real linear functional.
The proved characteristic-function injectivity identifies the input density
operator with that of a displaced vacuum.
-/

namespace GaussianTesting

noncomputable section

private theorem normalized_rotation_add
    {E : Type*} [AddCommGroup E] [Module ℝ E] {g F : E → ℂ}
    (hzero : g 0 = 1)
    (hrot : ∀ r s, F r = g ((Real.sqrt 2)⁻¹ • (r+s)) *
      g ((Real.sqrt 2)⁻¹ • (r-s))) (x y : E) : g (x+y) = g x * g y := by
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hcc : c*c = 1/2 := by
    dsimp [c]
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  let r := c • (x+y)
  let s := c • (x-y)
  have hr : c • (r+r) = x+y := by
    dsimp [r]
    simp only [smul_add, smul_smul, hcc]
    module
  have hx : c • (r+s) = x := by
    dsimp [r,s]
    simp only [smul_add, smul_sub, smul_smul, hcc]
    module
  have hy : c • (r-s) = y := by
    dsimp [r,s]
    simp only [smul_add, smul_sub, smul_smul, hcc]
    module
  have h1 := hrot r r
  have h2 := hrot r s
  change F r = g (c • (r+r)) * g (c • (r-r)) at h1
  change F r = g (c • (r+s)) * g (c • (r-s)) at h2
  rw [hr, sub_self, smul_zero, hzero, mul_one] at h1
  rw [hx, hy] at h2
  exact h1.symm.trans h2

/-- Actual beam-splitter factorization gives the equation used in the coherent
part of Proposition 6.3. -/
theorem coherent_factorization_characteristic_equation (m : ℕ)
    (ψ φ : WaveSpace m)
    (hfactor : (schrodingerTensorRotation m (Real.pi/4)).symm (hilbertTmul ψ ψ) =
      hilbertTmul φ (waveVacuum m)) (r s : WavePhase m) :
    pureWaveCharacteristic m φ r * vacuumCharacteristic s =
      pureWaveCharacteristic m ψ ((Real.sqrt 2)⁻¹ • (r+s)) *
        pureWaveCharacteristic m ψ ((Real.sqrt 2)⁻¹ • (r-s)) := by
  have h := pureTensorCharacteristic_balanced_product m ψ ψ r s
  rw [hfactor, pureTensorCharacteristic_tmul, pureWaveCharacteristic_vacuum] at h
  exact h.trans (mul_comm _ _)

/-- Dividing the physical characteristic equation by the nonvanishing vacuum
function yields exactly the manuscript's normalized equation. -/
theorem coherent_factorization_normalized_equation (m : ℕ)
    (ψ φ : WaveSpace m)
    (hfactor : (schrodingerTensorRotation m (Real.pi/4)).symm (hilbertTmul ψ ψ) =
      hilbertTmul φ (waveVacuum m)) (r s : WavePhase m) :
    pureWaveCharacteristic m φ r / vacuumCharacteristic r =
      (pureWaveCharacteristic m ψ ((Real.sqrt 2)⁻¹ • (r+s)) /
          vacuumCharacteristic ((Real.sqrt 2)⁻¹ • (r+s))) *
        (pureWaveCharacteristic m ψ ((Real.sqrt 2)⁻¹ • (r-s)) /
          vacuumCharacteristic ((Real.sqrt 2)⁻¹ • (r-s))) := by
  rw [div_mul_div_comm, ← vacuumCharacteristic_balanced,
    ← coherent_factorization_characteristic_equation m ψ φ hfactor]
  exact (mul_div_mul_right _ _ (vacuumCharacteristic_ne_zero s)).symm

/-- The normalized characteristic function of a unit input with vacuum in the
second output is a continuous unit-circle character. -/
theorem coherent_factorization_normalized_character (m : ℕ)
    (ψ φ : WaveSpace m) (hψ : ‖ψ‖ = 1)
    (hfactor : (schrodingerTensorRotation m (Real.pi/4)).symm (hilbertTmul ψ ψ) =
      hilbertTmul φ (waveVacuum m)) :
    let g := fun r => pureWaveCharacteristic m ψ r / vacuumCharacteristic r
    Continuous g ∧ g 0 = 1 ∧ (∀ r s, g (r+s) = g r * g s) ∧
      (∀ r, ‖g r‖ = 1) := by
  let g := fun r => pureWaveCharacteristic m ψ r / vacuumCharacteristic r
  have hgzero : g 0 = 1 := by simp [g, hψ]
  have hgadd (r s : WavePhase m) : g (r+s) = g r * g s :=
    normalized_rotation_add hgzero (coherent_factorization_normalized_equation m ψ φ hfactor) r s
  have hgneg (r : WavePhase m) : g (-r) = star (g r) := by
    dsimp [g]
    rw [pureWaveCharacteristic_neg, vacuumCharacteristic_neg, map_div₀]
    congr 1
    exact (Complex.conj_ofReal _).symm
  refine ⟨?_, hgzero, hgadd, ?_⟩
  · apply (continuous_pureWaveCharacteristic m ψ).div ?_ vacuumCharacteristic_ne_zero
    unfold vacuumCharacteristic
    fun_prop
  · intro r
    have h := hgadd r (-r)
    rw [add_neg_cancel, hgzero, hgneg] at h
    have hn : 1 = ‖g r‖ * ‖g r‖ := by
      simpa only [norm_mul, norm_star, norm_one] using congrArg norm h
    nlinarith only [hn, norm_nonneg (g r)]

/-- The characteristic function is the vacuum Gaussian times a linear phase,
derived from the actual splitter factorization. -/
theorem coherent_factorization_characteristic_linear (m : ℕ)
    (ψ φ : WaveSpace m) (hψ : ‖ψ‖ = 1)
    (hfactor : (schrodingerTensorRotation m (Real.pi/4)).symm (hilbertTmul ψ ψ) =
      hilbertTmul φ (waveVacuum m)) :
    ∃ L : WavePhase m →L[ℝ] ℝ, ∀ r,
      pureWaveCharacteristic m ψ r =
        vacuumCharacteristic r * Complex.exp (Complex.I * (L r : ℂ)) := by
  obtain ⟨hc, hz, ha, hn⟩ := coherent_factorization_normalized_character m ψ φ hψ hfactor
  obtain ⟨L, hL⟩ := continuous_character_eq_exp_linear hc hz ha hn
  refine ⟨L, fun r => ?_⟩
  have h := (div_eq_iff (vacuumCharacteristic_ne_zero r)).mp (hL r)
  exact h.trans (mul_comm _ _)

attribute [local irreducible] pureWaveCharacteristic schrodingerTensorRotation
  weylOperator waveVacuum vacuumCharacteristic

set_option maxHeartbeats 1200000 in
/-- The coherent converse in Proposition 6.3, starting from the physical
splitter factorization. Characteristic-function injectivity identifies the
pure state with a displaced vacuum, independently of its global phase. -/
theorem coherent_factorization_eq_displaced_vacuum (m : ℕ)
    (ψ φ : WaveSpace m) (hψ : ‖ψ‖ = 1)
    (hfactor : (schrodingerTensorRotation m (Real.pi/4)).symm (hilbertTmul ψ ψ) =
      hilbertTmul φ (waveVacuum m)) :
    ∃ a : WavePhase m,
      InnerProductSpace.rankOne ℂ ψ ψ =
        InnerProductSpace.rankOne ℂ (weylOperator m a (waveVacuum m))
          (weylOperator m a (waveVacuum m)) := by
  obtain ⟨L, hL⟩ := coherent_factorization_characteristic_linear m ψ φ hψ hfactor
  obtain ⟨a, ha⟩ := exists_waveSymplectic_eq_linear L
  refine ⟨a, rankOne_eq_of_pureWaveCharacteristic_eq _ _ (funext fun r => ?_)⟩
  rw [hL, pureWaveCharacteristic_displaced_vacuum, ha, mul_comm]

end
end GaussianTesting
