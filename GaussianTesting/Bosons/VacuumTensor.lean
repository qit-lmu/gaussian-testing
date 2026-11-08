module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerVacuum
public import GaussianTesting.Bosons.SchrodingerFourCopy

@[expose] public section

/-!
# Tensor-product vacuum and copy rotations

The product of two normalized vacuum wavefunctions is a radial Gaussian on
the two-copy position space. The actual coordinate rotations therefore fix
it, providing the common vacuum background used by Propositions 6.1 and 6.3.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

attribute [local irreducible] schrodingerTensorRotation waveVacuum hilbertTmul

private theorem vacuum_product_formula (m : ℕ) (z : BosonConfig m) :
    waveVacuumFun m (bosonPosition 0 z) * waveVacuumFun m (bosonPosition 1 z) =
      ((Real.pi ^ (-(m : ℝ)/4) : ℝ) : ℂ)^2 * (Real.exp (-‖z‖^2/2) : ℂ) := by
  have hn : ‖z‖^2 = ‖bosonPosition 0 z‖^2 + ‖bosonPosition 1 z‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two]
    rfl
  have he : -‖bosonPosition 0 z‖^2/2 + -‖bosonPosition 1 z‖^2/2 = -‖z‖^2/2 := by
    rw [hn]
    ring
  unfold waveVacuumFun
  calc
    _ = ((Real.pi ^ (-(m : ℝ)/4) : ℝ) : ℂ)^2 *
        ((Real.exp (-‖bosonPosition 0 z‖^2/2) : ℂ) *
          (Real.exp (-‖bosonPosition 1 z‖^2/2) : ℂ)) := by ring
    _ = _ := by rw [← Complex.ofReal_mul, ← Real.exp_add, he]

theorem waveTensor_vacuum_coeFn (m : ℕ) :
    (waveTensor m (hilbertTmul (waveVacuum m) (waveVacuum m)) : BosonConfig m → ℂ) =ᵐ[volume]
      fun z => ((Real.pi ^ (-(m : ℝ)/4) : ℝ) : ℂ)^2 *
        (Real.exp (-‖z‖^2/2) : ℂ) := by
  have hp := (bosonPositions_measurePreserving m).quasiMeasurePreserving
  filter_upwards [waveTensor_tmul_coeFn m (waveVacuum m) (waveVacuum m),
    (quasiMeasurePreserving_fst.comp hp).ae_eq_comp (waveVacuum_coeFn m),
    (quasiMeasurePreserving_snd.comp hp).ae_eq_comp (waveVacuum_coeFn m)] with z hz h0 h1
  simp only [Function.comp_apply] at h0 h1
  rw [hz, h0, h1]
  exact vacuum_product_formula m z

/-- The product vacuum is fixed by every physical copy rotation. -/
theorem schrodingerTensorRotation_vacuum (m : ℕ) (θ : ℝ) :
    schrodingerTensorRotation m θ (hilbertTmul (waveVacuum m) (waveVacuum m)) =
      hilbertTmul (waveVacuum m) (waveVacuum m) := by
  apply (waveTensorEquiv m).injective
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, waveTensorEquiv_apply]
  apply Lp.ext
  filter_upwards [schrodingerRotation_coeFn m θ
      (waveTensor m (hilbertTmul (waveVacuum m) (waveVacuum m))),
    (bosonRotation_measurePreserving m θ).quasiMeasurePreserving.ae_eq_comp
      (waveTensor_vacuum_coeFn m), waveTensor_vacuum_coeFn m] with z hz hr hv
  simp only [Function.comp_apply] at hr
  rw [hz, hr, hv, norm_bosonRotate]

end
end GaussianTesting
