module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerLambda
public import GaussianTesting.Bosons.SchrodingerTensor
public import GaussianTesting.Bosons.SignedSwapPurity
public import GaussianTesting.Bosons.ProjectionTrace

@[expose] public section

/-!
# Lemma 6.2 on actual Schrödinger wavefunctions

This is the manuscript statement for every positive trace-class density
operator on `L²(ℝᵐ)`. The physical product density is constructed through the
canonical product-wavefunction isometry, and the accepting projection is onto
the kernel of the graph closure of the specified finite Fock generator.

The proof follows the manuscript: rotations fix the closed kernel; the
quarter-turn is a signed swap; its trace is `Tr(Jρ²)`; and its modulus is at
most `Tr(ρ²) ≤ ‖ρ‖`. Hilbert bases appear only as coordinates for the
basis-independent trace, and are arbitrary.
-/

namespace GaussianTesting

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- Two independent copies of a physical density operator, represented on
actual product wavefunctions. -/
def schrodingerDensityTensor (m : ℕ) (ρ : WaveSpace m →L[ℂ] WaveSpace m) :
    SchrodingerSpace m →L[ℂ] SchrodingerSpace m :=
  HilbertDensity.embeddedTensor (waveTensor m) ρ

/-- The physical tensor density has the defining action on product wavefunctions. -/
theorem schrodingerDensityTensor_product (m : ℕ)
    (ρ : WaveSpace m →L[ℂ] WaveSpace m) (f g : WaveSpace m) :
    schrodingerDensityTensor m ρ (waveProduct m f g) =
      waveProduct m (ρ f) (ρ g) := by
  have hleft (v : HilbertSquare (WaveSpace m)) :
      (waveTensor m).toContinuousLinearMap.adjoint (waveTensor m v) = v :=
    DFunLike.congr_fun (waveTensor m).adjoint_comp_self v
  change waveTensor m (hilbertTensorMap ρ ρ
    ((waveTensor m).toContinuousLinearMap.adjoint (waveTensor m (hilbertTmul f g)))) = _
  rw [hleft, hilbertTensorMap_tmul]
  rfl

variable {m : ℕ} {κ ν : Type*}

/-- The complex trace in the acceptance hypothesis is real. -/
theorem schrodinger_acceptance_real {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsDensityOperator b ρ) :
    HilbertDensity.operatorTrace c (schrodingerDensityTensor m ρ * schrodingerP0 m) =
      ((HilbertDensity.operatorTrace c
        (schrodingerDensityTensor m ρ * schrodingerP0 m)).re : ℂ) :=
  (hρ.embeddedTensor c (waveTensor m)).toIsPositiveTraceClass.trace_starProjection_real
    (schrodingerLambda m).ker

/-- The manuscript's mixed-state acceptance is a probability in `[0,1]`. -/
theorem schrodinger_acceptance_mem_Icc {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsDensityOperator b ρ) :
    (HilbertDensity.operatorTrace c (schrodingerDensityTensor m ρ * schrodingerP0 m)).re ∈
      Set.Icc (0 : ℝ) 1 :=
  (hρ.embeddedTensor c (waveTensor m)).trace_starProjection_probability
    (schrodingerLambda m).ker

/-- The signed-swap trace identity in the second line of Lemma 6.2's proof,
with actual wavefunction rotation and reflection. -/
theorem schrodinger_signedSwap_trace {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) :
    HilbertDensity.operatorTrace c
      ((schrodingerRotation m (Real.pi / 2)).toContinuousLinearEquiv.toContinuousLinearMap *
        schrodingerDensityTensor m ρ) =
      HilbertDensity.operatorTrace b
        ((waveParity m).toContinuousLinearEquiv.toContinuousLinearMap * (ρ * ρ)) :=
  HilbertDensity.signedSwap_trace c hρ (waveTensor m) (waveParity m)
    (schrodingerRotation m (Real.pi / 2)) (schrodingerRotation_quarter_waveTensor m)

/-- **Lemma 6.2.** Any positive trace-class operator of trace one on actual
`L²(ℝᵐ)` whose two-copy kernel test accepts with probability at least `1 - τ`
has operator norm at least `1 - 2τ`. No Gram family, intertwining relation,
kernel-identification hypothesis, or moment assumption is required. -/
theorem purity_schrodinger {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsDensityOperator b ρ) {τ : ℝ}
    (hp : 1 - τ ≤ (HilbertDensity.operatorTrace c
      (schrodingerDensityTensor m ρ * schrodingerP0 m)).re) :
    1 - 2 * τ ≤ ‖ρ‖ := by
  apply HilbertDensity.purity_of_signedSwap c hρ (waveTensor m) (waveParity m)
    (schrodingerRotation m (Real.pi / 2)) (schrodingerRotation_quarter_waveTensor m)
    (schrodingerP0 m) (schrodingerP0_symmetric m) (schrodingerP0_idempotent m)
    (schrodingerRotation_P0 m (Real.pi / 2))
  rw [(hρ.embeddedTensor c (waveTensor m)).toIsPositiveTraceClass.operatorTrace_mul_comm]
  exact hp

end
end GaussianTesting
