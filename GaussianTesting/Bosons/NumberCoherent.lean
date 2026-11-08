module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberRotation
public import GaussianTesting.Bosons.SchrodingerCoherent
public import GaussianTesting.Bosons.CoherentSpectrum
public import GaussianTesting.GradientFlow.HilbertPairOperators

@[expose] public section

/-! # The physical coherent projection in occupation coordinates -/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

private theorem numberCoordinates_vacuumProjection (m : ℕ) (g : WaveSpace m) :
    (fockSchrodingerEquiv m).symm (waveVacuumProjection m g) =
      ((fockSchrodingerEquiv m).symm g) (fun _ => 0) • lp.single 2 (fun _ : Fin m => 0) 1 := by
  classical
  have hv : (fockSchrodingerEquiv m).symm (waveVacuum m) =
      lp.single 2 (fun _ : Fin m => 0) 1 := by
    apply (fockSchrodingerEquiv m).injective
    rw [LinearIsometryEquiv.apply_symm_apply, fockSchrodingerEquiv_vacuum]
  have hi : inner ℂ (waveVacuum m) g = ((fockSchrodingerEquiv m).symm g) (fun _ => 0) := by
    rw [← (fockSchrodingerEquiv m).symm.inner_map_map, hv, lp.inner_single_left]
    simp
  rw [waveVacuumProjection_apply, map_smul, hv, hi]

private theorem vacProj_tpPair (m : ℕ) (f g : FockB m) :
    vacProj m (tpPair f g) =
      tpPair f (g (fun _ => 0) • lp.single 2 (fun _ : Fin m => 0) 1) := by
  classical
  apply lp.ext
  funext p
  simp only [vacProj_apply, tpPair_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all

/-- Vacuum in the second physical register is exactly zero occupation in that register. -/
theorem waveNumberCoordinates_vacuumSecond (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m
      (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m)) (waveVacuumProjection m) v) =
        vacProj m (waveNumberCoordinates m v) := by
  let C := (waveNumberCoordinates m).toContinuousLinearEquiv.toContinuousLinearMap
  have he : C.comp
      (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m)) (waveVacuumProjection m)) =
        (vacProj m).comp C := by
    apply hilbertTensor_ext
    intro f g
    change waveNumberCoordinates m
      (hilbertTensorMap (ContinuousLinearMap.id ℂ (WaveSpace m)) (waveVacuumProjection m)
        (hilbertTmul f g)) = vacProj m (waveNumberCoordinates m (hilbertTmul f g))
    simp only [hilbertTensorMap_tmul, ContinuousLinearMap.id_apply,
      waveNumberCoordinates, hilbertCoords_tmul, numberCoordinates_vacuumProjection,
      vacProj_tpPair]
  exact DFunLike.congr_fun he v

/-- The physical positive balanced splitter is `ULp` in number coordinates. -/
theorem waveNumberCoordinates_rotation (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m (schrodingerTensorRotation m (Real.pi/4) v) =
      ULp m (waveNumberCoordinates m v) := by
  apply (fockPairSchrodingerEquiv m).injective
  rw [fockPairSchrodingerEquiv_waveNumberCoordinates,
    fockPairSchrodingerEquiv_ULp, fockPairSchrodingerEquiv_waveNumberCoordinates]
  change waveTensorEquiv m (schrodingerTensorRotation m (Real.pi/4) v) =
    schrodingerRotation m (Real.pi/4) (waveTensorEquiv m v)
  simp only [schrodingerTensorRotation, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- The inverse physical splitter is `VLp` in number coordinates. -/
theorem waveNumberCoordinates_rotation_symm (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m ((schrodingerTensorRotation m (Real.pi/4)).symm v) =
      VLp m (waveNumberCoordinates m v) := by
  have h := waveNumberCoordinates_rotation m ((schrodingerTensorRotation m (Real.pi/4)).symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have he := congrArg (VLp m) h
  have hi := DFunLike.congr_fun (VLp_ULp m)
    (waveNumberCoordinates m ((schrodingerTensorRotation m (Real.pi/4)).symm v))
  change VLp m (ULp m _) = _ at hi
  rw [hi] at he
  exact he.symm

/-- The physical coherent accepting projection is precisely `QB` in occupation coordinates. -/
theorem waveNumberCoordinates_Q (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m (schrodingerQ m v) = QB m (waveNumberCoordinates m v) := by
  simp only [schrodingerQ, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [waveNumberCoordinates_rotation, waveNumberCoordinates_vacuumSecond,
    waveNumberCoordinates_rotation_symm, QB_eq_conj]
  rfl

/-- Exact conjugation of the physical coherent-state observable. -/
theorem waveNumberCoordinates_conj_Q (m : ℕ) :
    (waveNumberCoordinates m).conjStarAlgEquiv (schrodingerQ m) = QB m := by
  ext f : 1
  change waveNumberCoordinates m (schrodingerQ m ((waveNumberCoordinates m).symm f)) = QB m f
  rw [waveNumberCoordinates_Q, LinearIsometryEquiv.apply_symm_apply]

/-- The three pairwise physical coherent tests averaged on the completed tensor cube. -/
def schrodingerCoherentAverage (m : ℕ) :
    HilbertCube (WaveSpace m) →L[ℂ] HilbertCube (WaveSpace m) :=
  (3 : ℂ)⁻¹ • (threeCopyPair12 (schrodingerQ m) + threeCopyPair13 (schrodingerQ m) +
    threeCopyPair23 (schrodingerQ m))

/-- Unitary number coordinates preserve the full spectrum of the physical three-copy average. -/
private theorem hilbertAverage_spectrum_eq {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : H ≃ₗᵢ[ℂ] L2 ι) {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) :
    spectrum ℂ (hilbertAverage e hP) =
      spectrum ℂ (Slp (hilbertPairOpCoords_isAcceptance e hP).norm_le_one) :=
  AlgEquiv.spectrum_eq
    (hilbertCoords e (hilbertCoords e e)).symm.conjStarAlgEquiv.toAlgEquiv _

private theorem Slp_congr {ι : Type*}
    {P Q : L2 (ι × ι) →L[ℂ] L2 (ι × ι)} (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (h : P = Q) : Slp hP = Slp hQ := by
  subst Q
  rfl

/-- Unitary number coordinates preserve the full spectrum of the physical three-copy average. -/
theorem schrodingerCoherentAverage_spectrum (m : ℕ) :
    spectrum ℂ (schrodingerCoherentAverage m) = spectrum ℂ (Slp (QB_norm_le_one m)) := by
  have hQ : hilbertPairOpCoords (fockSchrodingerEquiv m).symm (schrodingerQ m) = QB m :=
    waveNumberCoordinates_conj_Q m
  have hA : schrodingerCoherentAverage m =
      hilbertAverage (fockSchrodingerEquiv m).symm (schrodingerQ_isAcceptance m) :=
    (hilbertAverage_eq_threeCopyPairs (fockSchrodingerEquiv m).symm
      (schrodingerQ_isAcceptance m)).symm
  exact (congrArg (spectrum ℂ) hA).trans <|
    (hilbertAverage_spectrum_eq (fockSchrodingerEquiv m).symm (schrodingerQ_isAcceptance m)).trans <|
      congrArg (spectrum ℂ) (Slp_congr _ (QB_norm_le_one m) hQ)

/-- Lemma 6.6's spectral inclusion for the actual physical coherent-state test. -/
theorem schrodinger_coherent_spectrum_subset (m : ℕ) :
    spectrum ℂ (schrodingerCoherentAverage m) ⊆
      Complex.ofReal '' Set.Icc 0 (1 / 2) ∪ {1} := by
  exact (schrodingerCoherentAverage_spectrum m).le.trans (coherent_spectrum_subset m)

end
end GaussianTesting
