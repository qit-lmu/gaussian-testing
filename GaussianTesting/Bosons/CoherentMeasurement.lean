module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerNumberBasis
public import GaussianTesting.Bosons.SchrodingerCoherent

@[expose] public section

/-!
# The total-number readout in Figure 1(c)

Total particle number is read in the proved oscillator number basis: an
occupation vector `n` has outcome `∑ j, n j`. Its zero-outcome projection is
the vacuum projection. Applying the inverse balanced splitter and measuring
this outcome in register two therefore has precisely the manuscript's
coherent accepting observable `Q` and probability `q`.
-/

namespace GaussianTesting

open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The total-count outcome `k` retains exactly occupation vectors whose
mode occupation numbers sum to `k`. -/
def occupationNumberProjection (m k : ℕ) : FockB m →L[ℂ] FockB m := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => if degB n = k then f n else 0, ?_⟩
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · apply (lp.memℓp f).mono'
    intro n
    split_ifs <;> simp
  · intro f g
    apply lp.ext
    funext n
    simp only [lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp
  · intro z f
    apply lp.ext
    funext n
    change (if _ then _ else _) = _
    split_ifs <;> simp_all [Pi.smul_apply]
  · intro f
    simp only [one_mul]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    change ‖if degB n = k then f n else 0‖ ≤ ‖f n‖
    split_ifs <;> simp

@[simp] theorem occupationNumberProjection_apply (m k : ℕ)
    (f : FockB m) (n : Fin m → ℕ) :
    occupationNumberProjection m k f n = if degB n = k then f n else 0 := rfl

/-- Actual total-number measurement outcomes in the Schrödinger Hilbert space,
using the oscillator number basis whose completeness is proved. -/
def waveTotalNumberProjection (m k : ℕ) : WaveSpace m →L[ℂ] WaveSpace m :=
  (fockSchrodingerEquiv m).conjStarAlgEquiv (occupationNumberProjection m k)

/-- Total occupation is zero exactly when every mode is unoccupied. -/
theorem degB_eq_zero_iff {m : ℕ} (n : Fin m → ℕ) :
    degB n = 0 ↔ n = (fun _ => 0) := by
  classical
  simp only [degB, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

private theorem occupationNumberProjection_zero (m : ℕ) (f : FockB m) :
    occupationNumberProjection m 0 f = f (fun _ => 0) • lp.single 2 (fun _ : Fin m => 0) 1 := by
  classical
  apply lp.ext
  funext n
  simp only [occupationNumberProjection_apply, degB_eq_zero_iff, lp.coeFn_smul,
    Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with h
  · subst n; simp
  · simp_all

/-- Zero total particle number is exactly the vacuum outcome, for every mode
count, including the zero-mode Hilbert space. -/
theorem waveTotalNumberProjection_zero (m : ℕ) :
    waveTotalNumberProjection m 0 = waveVacuumProjection m := by
  classical
  ext f : 1
  apply (fockSchrodingerEquiv m).symm.injective
  have hv : (fockSchrodingerEquiv m).symm (waveVacuum m) =
      lp.single 2 (fun _ : Fin m => 0) 1 := by
    apply (fockSchrodingerEquiv m).injective
    rw [LinearIsometryEquiv.apply_symm_apply, fockSchrodingerEquiv_vacuum]
  have hi : inner ℂ (waveVacuum m) f = ((fockSchrodingerEquiv m).symm f) (fun _ => 0) := by
    rw [← (fockSchrodingerEquiv m).symm.inner_map_map, hv, lp.inner_single_left]
    simp
  simp only [waveTotalNumberProjection, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, occupationNumberProjection_zero,
    waveVacuumProjection_apply, map_smul, hv, hi]

/-- Figure 1(c): apply `U_{-π/4}`, discard register one, and accept precisely
when the total particle count in register two is zero. -/
def coherentNumberMeasurement (m : ℕ) :
    HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m) :=
  (schrodingerTensorRotation m (Real.pi / 4)).conjStarAlgEquiv
    (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m))
      (waveTotalNumberProjection m 0))

/-- The circuit's number-readout event is the physical coherent test `Q`. -/
theorem coherentNumberMeasurement_eq_Q (m : ℕ) :
    coherentNumberMeasurement m = schrodingerQ m := by
  rw [coherentNumberMeasurement, waveTotalNumberProjection_zero]
  rfl

/-- **Figure 1(c).** The accepting Born probability of the explicit
zero-total-count circuit is the coherent acceptance probability `q(ψ)`. -/
theorem coherentNumberMeasurement_acceptance {m : ℕ} (ψ : WaveSpace m) :
    (inner ℂ (hilbertTmul ψ ψ)
      (coherentNumberMeasurement m (hilbertTmul ψ ψ))).re =
        schrodingerCoherentAcceptance ψ := by
  rw [coherentNumberMeasurement_eq_Q]
  rfl

end
end GaussianTesting
