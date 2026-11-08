module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Weyl
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

/-!
# Matrix coordinates for the required symplectic actions

These identifications connect block matrices in position/momentum order to
actual Euclidean displacement parameters. They support Weyl covariance of
Gaussian unitaries; no metaplectic or exponential interpretation is used.
-/

namespace GaussianTesting

open Matrix

noncomputable section

/-- Join position and momentum coordinates, in this order. -/
def joinWavePhase {m : ℕ} (r : WavePhase m) : (Fin m ⊕ Fin m) → ℝ :=
  Sum.elim r.1 r.2

/-- Split position and momentum coordinates. -/
def splitWavePhase {m : ℕ} (v : (Fin m ⊕ Fin m) → ℝ) : WavePhase m :=
  (WithLp.toLp 2 (v ∘ Sum.inl), WithLp.toLp 2 (v ∘ Sum.inr))

@[simp] theorem join_splitWavePhase {m : ℕ} (v : (Fin m ⊕ Fin m) → ℝ) :
    joinWavePhase (splitWavePhase v) = v := by
  funext i
  cases i <;> rfl

@[simp] theorem split_joinWavePhase {m : ℕ} (r : WavePhase m) :
    splitWavePhase (joinWavePhase r) = r := by
  rfl

/-- A phase-space matrix acts on the actual pair of Euclidean parameters. -/
def phaseMatrixAction {m : ℕ} (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (r : WavePhase m) : WavePhase m := splitWavePhase (S *ᵥ joinWavePhase r)

@[simp] theorem phaseMatrixAction_one {m : ℕ} (r : WavePhase m) :
    phaseMatrixAction 1 r = r := by simp [phaseMatrixAction]

theorem phaseMatrixAction_mul {m : ℕ}
    (S T : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) (r : WavePhase m) :
    phaseMatrixAction (S*T) r = phaseMatrixAction S (phaseMatrixAction T r) := by
  simp only [phaseMatrixAction, join_splitWavePhase, mulVec_mulVec]

/-- A real matrix as a continuous map of position coordinates. -/
def waveMatrixCLM {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    WaveConfig m →L[ℝ] WaveConfig m := A.toEuclideanLin.toContinuousLinearMap

@[simp] theorem waveMatrixCLM_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (x : WaveConfig m) : waveMatrixCLM A x = WithLp.toLp 2 (A *ᵥ x) := rfl

theorem phaseMatrixAction_fromBlocks {m : ℕ} (A B C D : Matrix (Fin m) (Fin m) ℝ)
    (r : WavePhase m) :
    phaseMatrixAction (fromBlocks A B C D) r =
      (waveMatrixCLM A r.1 + waveMatrixCLM B r.2,
        waveMatrixCLM C r.1 + waveMatrixCLM D r.2) := by
  ext i <;> simp [phaseMatrixAction, splitWavePhase, joinWavePhase,
    fromBlocks_mulVec, waveMatrixCLM_apply]

/-- Invertible real matrices give continuous equivalences of position space. -/
def waveMatrixEquiv {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : IsUnit A) :
    WaveConfig m ≃L[ℝ] WaveConfig m := by
  let : Invertible A := hA.invertible
  exact LinearEquiv.toContinuousLinearEquiv
    { A.toEuclideanLin with
      invFun := A⁻¹.toEuclideanLin
      left_inv := by intro x; ext i; simp [Matrix.toLpLin_apply, mulVec_mulVec]
      right_inv := by intro x; ext i; simp [Matrix.toLpLin_apply, mulVec_mulVec] }

@[simp] theorem waveMatrixEquiv_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : IsUnit A) (x : WaveConfig m) : waveMatrixEquiv A hA x = waveMatrixCLM A x := rfl

@[simp] theorem waveMatrixEquiv_symm_apply {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : IsUnit A) (x : WaveConfig m) :
    (waveMatrixEquiv A hA).symm x = waveMatrixCLM A⁻¹ x := rfl

/-- Transpose is the real Euclidean adjoint. -/
theorem waveMatrixCLM_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    waveMatrixCLM Aᵀ = (waveMatrixCLM A).adjoint := by
  apply ContinuousLinearMap.coe_injective
  change Aᵀ.toEuclideanLin = A.toEuclideanLin.adjoint
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

/-- A symmetric matrix supplies the symmetric map used by a quadratic phase. -/
theorem waveMatrixCLM_symmetric {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsSymm) : (waveMatrixCLM A).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq

end
end GaussianTesting
