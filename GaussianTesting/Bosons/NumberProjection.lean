module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberTensor
public import GaussianTesting.Bosons.SchrodingerFourCopy

@[expose] public section

/-! # Physical tensor coordinates and the bosonic kernel projection -/

namespace GaussianTesting

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Occupation coordinates of the actual completed two-copy Hilbert space. -/
def waveNumberCoordinates (m : ℕ) : HilbertSquare (WaveSpace m) ≃ₗᵢ[ℂ] FockB2 m :=
  hilbertCoords (fockSchrodingerEquiv m).symm (fockSchrodingerEquiv m).symm

/-- Number coordinates and actual product wavefunctions give the same completed-tensor map. -/
theorem fockPairSchrodingerEquiv_waveNumberCoordinates (m : ℕ)
    (v : HilbertSquare (WaveSpace m)) :
    fockPairSchrodingerEquiv m (waveNumberCoordinates m v) = waveTensor m v := by
  apply hilbertTensor_induction
    (isClosed_eq ((fockPairSchrodingerEquiv m).continuous.comp
      (waveNumberCoordinates m).continuous) (waveTensor m).continuous) ?_ ?_ v
  · intro f g
    exact (congrArg (fockPairSchrodingerEquiv m)
      (hilbertCoords_tmul (fockSchrodingerEquiv m).symm (fockSchrodingerEquiv m).symm f g)).trans <|
      (fockPairSchrodingerEquiv_tpPair m ((fockSchrodingerEquiv m).symm f)
        ((fockSchrodingerEquiv m).symm g)).trans <|
      congrArg (waveTensor m) (congrArg₂ (fun x y : WaveSpace m => hilbertTmul x y)
        ((fockSchrodingerEquiv m).apply_symm_apply f)
        ((fockSchrodingerEquiv m).apply_symm_apply g))
  · intro a b ha hb
    simp only [Function.comp_apply] at ha hb ⊢
    simp only [map_add, ha, hb]

/-- The physical tensor projection and the number-basis projection are exactly conjugate. -/
theorem waveNumberCoordinates_P0 (m : ℕ) (v : HilbertSquare (WaveSpace m)) :
    waveNumberCoordinates m (schrodingerTensorP0 m v) = P0B m (waveNumberCoordinates m v) := by
  apply (fockPairSchrodingerEquiv m).injective
  rw [fockPairSchrodingerEquiv_waveNumberCoordinates,
    fockPairSchrodingerEquiv_P0B, fockPairSchrodingerEquiv_waveNumberCoordinates]
  change waveTensorEquiv m (schrodingerTensorP0 m v) =
    schrodingerP0 m (waveTensorEquiv m v)
  simp only [schrodingerTensorP0, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]

/-- Equality of the accepting observables after unitary conjugation. -/
theorem waveNumberCoordinates_conj_P0 (m : ℕ) :
    (waveNumberCoordinates m).conjStarAlgEquiv (schrodingerTensorP0 m) = P0B m := by
  ext f : 1
  change waveNumberCoordinates m
    (schrodingerTensorP0 m ((waveNumberCoordinates m).symm f)) = P0B m f
  rw [waveNumberCoordinates_P0, LinearIsometryEquiv.apply_symm_apply]

end
end GaussianTesting
