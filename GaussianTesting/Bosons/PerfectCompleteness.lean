module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.PerfectCompleteness
public import GaussianTesting.Bosons.GaussianSquareSpan
public import GaussianTesting.Bosons.SchrodingerCircuitSwap
public import GaussianTesting.Bosons.SchrodingerMeanZeroAcceptance

@[expose] public section

/-!
# Optimality of the centered bosonic Gaussian test on identical inputs

The span of Gaussian squares is the symmetric part of the closed kernel.
Although the full kernel can contain antisymmetric vectors, its projection
agrees with the span projection on identical inputs: the kernel projection
commutes with register swap. The manuscript's actual `P₀` therefore minimizes
acceptance among all perfectly complete positive contraction effects.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] waveTensorEquiv

local instance (m : ℕ) : CompleteSpace (meanZeroGaussianSquareSpan m) :=
  (isClosed_meanZeroGaussianSquareSpan m).isComplete.completeSpace_coe

private theorem projection_acceptance_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    {A : H →L[ℂ] H} (hle : M.starProjection ≤ A) (x : H) :
    (inner ℂ x (M.starProjection x)).re ≤ (inner ℂ x (A x)).re := by
  have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hle)).re_inner_nonneg_right x
  change 0 ≤ (inner ℂ x ((A - M.starProjection) x)).re at h
  rw [sub_apply, inner_sub_right, Complex.sub_re] at h
  exact sub_nonneg.mp h

private theorem gaussianSquareSpan_projection_eq_P0 (m : ℕ)
    (hspan : ∀ f : SchrodingerSpace m, f ∈ meanZeroGaussianSquareSpan m ↔
      f ∈ (schrodingerLambda m).ker ∧ schrodingerCopySwap m f = f)
    (ψ : WaveSpace m) :
    (meanZeroGaussianSquareSpan m).starProjection (waveTensorEquiv m (hilbertTmul ψ ψ)) =
      schrodingerP0 m (waveTensorEquiv m (hilbertTmul ψ ψ)) := by
  let x := hilbertTmul ψ ψ
  have hproj : waveTensorEquiv m (schrodingerTensorP0 m x) =
      schrodingerP0 m (waveTensorEquiv m x) := by
    simp only [schrodingerTensorP0, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
  have hswap : hilbertSwap (schrodingerTensorP0 m x) = schrodingerTensorP0 m x := by
    have h := (schrodingerTensorP0_isAcceptance m).swap_comm x
    change schrodingerTensorP0 m (hilbertSwap x) = hilbertSwap (schrodingerTensorP0 m x) at h
    rw [show hilbertSwap x = x from hilbertSwap_tmul ψ ψ] at h
    exact h.symm
  apply (meanZeroGaussianSquareSpan m).eq_starProjection_of_mem_of_inner_eq_zero
  · apply (hspan _).mpr
    constructor
    · exact (schrodingerLambda m).ker.starProjection_apply_mem _
    · rw [← hproj]
      simp only [waveTensorEquiv_apply, schrodingerCopySwap_waveTensor, hswap]
  · intro w hw
    exact (schrodingerLambda m).ker.starProjection_inner_eq_zero _ w ((hspan w).mp hw).1

private theorem bosonic_optimality_of_span (m : ℕ)
    (hspan : ∀ f : SchrodingerSpace m, f ∈ meanZeroGaussianSquareSpan m ↔
      f ∈ (schrodingerLambda m).ker ∧ schrodingerCopySwap m f = f)
    (A : HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m))
    (hA : 0 ≤ A) (hAnorm : ‖A‖ ≤ 1)
    (hcomplete : ∀ φ ∈ meanZeroGaussianWaveStates m,
      (hilbertTensorSquare (WaveSpace m)).accProbA A φ = 1) (ψ : WaveSpace m) :
    schrodingerMeanZeroAcceptance ψ ≤ (hilbertTensorSquare (WaveSpace m)).accProbA A ψ := by
  let E : HilbertSquare (WaveSpace m) ≃ₗᵢ[ℂ] SchrodingerSpace m := waveTensorEquiv m
  let B : SchrodingerSpace m →L[ℂ] SchrodingerSpace m := E.conjStarAlgEquiv A
  have hB : 0 ≤ B := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    change (E.toLinearMap ∘ₗ A.toLinearMap ∘ₗ E.symm.toLinearMap).IsPositive
    exact (LinearMap.isPositive_linearIsometryEquiv_conj_iff E).mpr
      (ContinuousLinearMap.nonneg_iff_isPositive.mp hA).toLinearMap
  have hBnorm : ‖B‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound B (by norm_num : (0 : ℝ) ≤ 1)
    intro y
    change ‖E (A (E.symm y))‖ ≤ 1 * ‖y‖
    rw [E.norm_map]
    calc
      ‖A (E.symm y)‖ ≤ ‖A‖ * ‖E.symm y‖ := A.le_opNorm (E.symm y)
      _ ≤ 1 * ‖y‖ := by rw [E.symm.norm_map]; gcongr
  let S := (fun φ : WaveSpace m => E (hilbertTmul φ φ)) '' meanZeroGaussianWaveStates m
  have hcomplete' : ∀ y ∈ S, (inner ℂ y (B y)).re = ‖y‖ ^ 2 := by
    rintro y ⟨φ,hφ,rfl⟩
    have hnorm : ‖hilbertTmul φ φ‖ = 1 := by
      change ‖(hilbertTensorSquare (WaveSpace m)).tp φ φ‖ = 1
      rw [TensorSquare.norm_tp, norm_eq_one_of_mem_meanZeroGaussianWaveStates hφ, one_mul]
    simpa only [B, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map,
      LinearIsometryEquiv.norm_map, hnorm, one_pow, TensorSquare.accProbA, hilbertTensorSquare]
      using hcomplete φ hφ
  have hle : (meanZeroGaussianSquareSpan m).starProjection ≤ B := by
    apply starProjection_le_of_fixes _ hB
    intro y hy
    exact effect_fixes_closedSpan (A := B) (S := S)
      (fun z hz => effect_fixes_of_acceptance_eq hBnorm (hcomplete' z hz)) hy
  have hnamed : (inner ℂ (E (hilbertTmul ψ ψ))
      ((meanZeroGaussianSquareSpan m).starProjection (E (hilbertTmul ψ ψ)))).re ≤
      (inner ℂ (E (hilbertTmul ψ ψ)) (B (E (hilbertTmul ψ ψ)))).re :=
    projection_acceptance_le _ hle _
  have hP : schrodingerP0 m (E (hilbertTmul ψ ψ)) = E (schrodingerTensorP0 m (hilbertTmul ψ ψ)) := by
    simp only [schrodingerTensorP0, E, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]
  change (inner ℂ (hilbertTmul ψ ψ) (schrodingerTensorP0 m (hilbertTmul ψ ψ))).re ≤
    (inner ℂ (hilbertTmul ψ ψ) (A (hilbertTmul ψ ψ))).re
  calc
    _ = (inner ℂ (E (hilbertTmul ψ ψ)) (E (schrodingerTensorP0 m (hilbertTmul ψ ψ)))).re :=
      congrArg Complex.re (E.inner_map_map _ _).symm
    _ = (inner ℂ (E (hilbertTmul ψ ψ)) (schrodingerP0 m (E (hilbertTmul ψ ψ)))).re :=
      congrArg (fun v => (inner ℂ (E (hilbertTmul ψ ψ)) v).re) hP.symm
    _ = (inner ℂ (E (hilbertTmul ψ ψ))
        ((meanZeroGaussianSquareSpan m).starProjection (E (hilbertTmul ψ ψ)))).re :=
      congrArg (fun v => (inner ℂ (E (hilbertTmul ψ ψ)) v).re)
        (gaussianSquareSpan_projection_eq_P0 m hspan ψ).symm
    _ ≤ (inner ℂ (E (hilbertTmul ψ ψ)) (B (E (hilbertTmul ψ ψ)))).re := hnamed
    _ = _ := by
      simp only [B, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]

/-- On identical inputs, the full closed-kernel projection agrees with the
projection onto the closed span of centered Gaussian squares. -/
theorem meanZeroGaussianSquareSpan_projection_square (m : ℕ) (ψ : WaveSpace m) :
    (meanZeroGaussianSquareSpan m).starProjection (waveTensorEquiv m (hilbertTmul ψ ψ)) =
      schrodingerP0 m (waveTensorEquiv m (hilbertTmul ψ ψ)) :=
  gaussianSquareSpan_projection_eq_P0 m (mem_meanZeroGaussianSquareSpan_iff m) ψ

/-- The Section 1 optimality assertion for the centered bosonic two-copy
test: every positive contraction accepting all centered pure Gaussian states
with probability one accepts every identical input at least as often as the
manuscript's actual closed-kernel test `P₀`. -/
theorem bosonicMeanZeroGaussian_optimality (m : ℕ)
    (A : HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m))
    (hA : 0 ≤ A) (hAnorm : ‖A‖ ≤ 1)
    (hcomplete : ∀ φ ∈ meanZeroGaussianWaveStates m,
      (hilbertTensorSquare (WaveSpace m)).accProbA A φ = 1) (ψ : WaveSpace m) :
    schrodingerMeanZeroAcceptance ψ ≤ (hilbertTensorSquare (WaveSpace m)).accProbA A ψ :=
  bosonic_optimality_of_span m (mem_meanZeroGaussianSquareSpan_iff m) A hA hAnorm hcomplete ψ

end

end GaussianTesting
