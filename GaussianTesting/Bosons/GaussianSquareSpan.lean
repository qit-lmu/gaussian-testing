module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GaussianSquareDensity
public import GaussianTesting.Bosons.CopyPolynomialInvariants
public import GaussianTesting.Bosons.PolynomialGaussianInjective
public import GaussianTesting.Bosons.RotationFixedSpace
public import GaussianTesting.Bosons.SchrodingerCircuitSwap

@[expose] public section

/-!
# The closed span of centered bosonic Gaussian squares

Average polynomial Gaussian vectors over copy rotations and then over swap.
The averaged polynomials lie in the Gram algebra, so their wavefunctions are
in the closed Gaussian-square span. Density gives every symmetric kernel
vector. Conversely every Gaussian square is symmetric and in the kernel.
-/

namespace GaussianTesting

open MeasureTheory MvPolynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

theorem schrodingerCopySwap_involution (m : ℕ) (f : SchrodingerSpace m) :
    schrodingerCopySwap m (schrodingerCopySwap m f) = f := by
  apply Lp.ext
  have hs := (bosonSwapPositions m).measurePreserving.quasiMeasurePreserving
  filter_upwards [schrodingerCopySwap_coeFn m (schrodingerCopySwap m f),
    hs.ae_eq_comp (schrodingerCopySwap_coeFn m f)] with z h₁ h₂
  have hz : bosonSwapPositions m (bosonSwapPositions m z) = z := by
    ext ⟨i,j⟩
    fin_cases i <;> rfl
  exact h₁.trans (by simpa only [Function.comp_apply, hz] using h₂)

/-- The physical copy swap agrees with the polynomial variable permutation. -/
theorem polynomialGaussian_copyModeSwap (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialGaussian (copyModeSwap m p) = schrodingerCopySwap m (polynomialGaussian p) := by
  apply Lp.ext
  have hs := (bosonSwapPositions m).measurePreserving.quasiMeasurePreserving
  filter_upwards [polynomialGaussian_coeFn (copyModeSwap m p),
    schrodingerCopySwap_coeFn m (polynomialGaussian p),
    hs.ae_eq_comp (polynomialGaussian_coeFn p)] with z h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃]
  simp only [polynomialGaussianFun, copyModeSwap, eval_rename,
    LinearIsometryEquiv.norm_map]
  congr 2
  congr 1
  funext ⟨a,j⟩
  fin_cases a <;> rfl

/-- The symmetric subspace in physical two-copy wavefunction coordinates. -/
def schrodingerSymmetricSpace (m : ℕ) : Submodule ℂ (SchrodingerSpace m) :=
  ((schrodingerCopySwap m).toContinuousLinearMap -
    ContinuousLinearMap.id ℂ (SchrodingerSpace m)).ker

@[simp] theorem mem_schrodingerSymmetricSpace (m : ℕ) (f : SchrodingerSpace m) :
    f ∈ schrodingerSymmetricSpace m ↔ schrodingerCopySwap m f = f := by
  change schrodingerCopySwap m f - f = 0 ↔ _
  exact sub_eq_zero

private def symmetricRotationAverage (m : ℕ) (f : SchrodingerSpace m) : SchrodingerSpace m :=
  (2 : ℂ)⁻¹ • (schrodingerRotationAverage m f +
    schrodingerCopySwap m (schrodingerRotationAverage m f))

private theorem symmetricRotationAverage_continuous (m : ℕ) :
    Continuous (symmetricRotationAverage m) := by
  unfold symmetricRotationAverage
  exact ((continuous_schrodingerRotationAverage m).add
    ((schrodingerCopySwap m).continuous.comp (continuous_schrodingerRotationAverage m))).const_smul
      ((2 : ℂ)⁻¹)

private theorem symmetricRotationAverage_rotation_fixed (m : ℕ)
    (f : SchrodingerSpace m) (θ : ℝ) :
    schrodingerRotation m θ (symmetricRotationAverage m f) = symmetricRotationAverage m f := by
  have hs := schrodingerCopySwap_rotation m (-θ) (schrodingerRotationAverage m f)
  rw [neg_neg, schrodingerRotationAverage_fixed] at hs
  simp only [symmetricRotationAverage, map_smul, map_add,
    schrodingerRotationAverage_fixed, hs.symm]

private theorem symmetricRotationAverage_swap_fixed (m : ℕ) (f : SchrodingerSpace m) :
    schrodingerCopySwap m (symmetricRotationAverage m f) = symmetricRotationAverage m f := by
  simp only [symmetricRotationAverage, map_smul, map_add, schrodingerCopySwap_involution]
  congr 1
  exact add_comm _ _

private theorem symmetricRotationAverage_eq_self (m : ℕ) (f : SchrodingerSpace m)
    (hf : f ∈ (schrodingerLambda m).ker) (hs : schrodingerCopySwap m f = f) :
    symmetricRotationAverage m f = f := by
  have hr := schrodingerRotationAverage_eq_self m f
    (schrodingerRotation_fixed_of_mem_kernel m hf)
  rw [symmetricRotationAverage, hr, hs, ← two_smul ℂ f, smul_smul]
  norm_num

private theorem symmetricRotationAverage_polynomialGaussian (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    ∃ q : MvPolynomial (Fin 2 × Fin m) ℂ,
      polynomialGaussian q = symmetricRotationAverage m (polynomialGaussian p) := by
  obtain ⟨q, hq⟩ := schrodingerRotationAverage_polynomialGaussian m p
  refine ⟨(2 : ℂ)⁻¹ • (q + copyModeSwap m q), ?_⟩
  change polynomialGaussianLinear _ = _
  rw [map_smul, map_add]
  change (2 : ℂ)⁻¹ • (polynomialGaussian q + polynomialGaussian (copyModeSwap m q)) = _
  rw [polynomialGaussian_copyModeSwap, hq]
  rfl

private theorem symmetricRotationAverage_polynomial_mem_span (m : ℕ)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    symmetricRotationAverage m (polynomialGaussian p) ∈ meanZeroGaussianSquareSpan m := by
  obtain ⟨q,hq⟩ := symmetricRotationAverage_polynomialGaussian m p
  have hr (θ : ℝ) : schrodingerRotation m θ (polynomialGaussian q) = polynomialGaussian q := by
    rw [hq]
    exact symmetricRotationAverage_rotation_fixed m _ θ
  have hΛ : polynomialLambda m q = 0 := by
    apply polynomialGaussian_injective
    exact (polynomialLambda_eq_zero_of_rotation_fixed m q hr).trans
      (polynomialGaussianLinear (ι := Fin 2 × Fin m)).map_zero.symm
  have hquarter : polynomialRotate m (Real.pi / 2) q = q := by
    apply polynomialGaussian_injective
    rw [polynomialGaussian_rotate, hr]
  have hswap : copyModeSwap m q = q := by
    apply polynomialGaussian_injective
    rw [polynomialGaussian_copyModeSwap, hq]
    exact symmetricRotationAverage_swap_fixed m _
  rw [← hq]
  exact polynomialGaussian_mem_meanZeroGaussianSquareSpan
    (polynomial_mem_copyGramAlgebra_of_invariant q hΛ hquarter hswap)

private theorem symmetricRotationAverage_mem_span (m : ℕ) (f : SchrodingerSpace m) :
    symmetricRotationAverage m f ∈ meanZeroGaussianSquareSpan m :=
  isClosed_property denseRange_polynomialGaussian
    ((isClosed_meanZeroGaussianSquareSpan m).preimage (symmetricRotationAverage_continuous m))
    (symmetricRotationAverage_polynomial_mem_span m) f

/-- The closed Gaussian-square span is exactly the symmetric part of the
kernel of the manuscript's closed two-copy generator. -/
theorem meanZeroGaussianSquareSpan_eq_symmetric_kernel (m : ℕ) :
    meanZeroGaussianSquareSpan m = (schrodingerLambda m).ker ⊓ schrodingerSymmetricSpace m := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨ψ, hψ, rfl⟩
      refine ⟨(mem_meanZeroGaussianWaveStates_iff_kernel ψ
        (norm_eq_one_of_mem_meanZeroGaussianWaveStates hψ)).mp hψ, ?_⟩
      apply (mem_schrodingerSymmetricSpace m _).mpr
      change schrodingerCopySwap m (waveTensor m (hilbertTmul ψ ψ)) =
        waveTensor m (hilbertTmul ψ ψ)
      rw [schrodingerCopySwap_waveTensor, hilbertSwap_tmul]
    · exact (schrodingerLambda_kernel_isClosed m).inter
        ((schrodingerCopySwap m).toContinuousLinearMap -
          ContinuousLinearMap.id ℂ (SchrodingerSpace m)).isClosed_ker
  · intro f hf
    have hs := (mem_schrodingerSymmetricSpace m f).mp hf.2
    simpa only [symmetricRotationAverage_eq_self m f hf.1 hs] using
      symmetricRotationAverage_mem_span m f

/-- Membership form of the Gaussian-square span theorem on actual wavefunctions. -/
theorem mem_meanZeroGaussianSquareSpan_iff (m : ℕ) (f : SchrodingerSpace m) :
    f ∈ meanZeroGaussianSquareSpan m ↔
      f ∈ (schrodingerLambda m).ker ∧ schrodingerCopySwap m f = f := by
  rw [meanZeroGaussianSquareSpan_eq_symmetric_kernel, Submodule.mem_inf,
    mem_schrodingerSymmetricSpace]

end
end GaussianTesting
