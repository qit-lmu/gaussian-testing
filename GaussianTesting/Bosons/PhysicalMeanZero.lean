module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.GaussianKernel
public import GaussianTesting.Bosons.VacuumTensor
public import GaussianTesting.Bosons.MeanZeroCharacteristic
public import GaussianTesting.Bosons.GaussianCharacteristicReconstruction
public import GaussianTesting.Bosons.GaussianWaveStates
public import GaussianTesting.GradientFlow.RankOneTensor

@[expose] public section

/-!
# Physical Gaussian certainty in Proposition 6.1

The vacuum is in the finite generator kernel because its polynomial factor is
constant. Symplectic invariance then gives the same conclusion for the centered
Gaussian vacuum orbit, exactly as in the manuscript's forward implication.
For the converse, the manuscript's balanced characteristic-function equation
gives a centered quadratic exponent. Fourier reconstruction identifies its
wavefunction with the independent symplectic vacuum orbit. The resulting
three-way equivalence uses the actual graph-closed generator and its kernel
projection throughout.
-/

namespace GaussianTesting

open MeasureTheory

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The product vacuum lies in the prescribed closed kernel, already on its
finite domain: the coordinate annihilators kill the constant polynomial. -/
theorem waveTensor_vacuum_mem_kernel (m : ℕ) :
    waveTensorEquiv m (hilbertTmul (waveVacuum m) (waveVacuum m)) ∈
      (schrodingerLambda m).ker := by
  let p : MvPolynomial (Fin 2 × Fin m) ℂ :=
    MvPolynomial.C (((Real.pi ^ (-(m : ℝ)/4) : ℝ) : ℂ)^2)
  have hp : polynomialGaussian p =
      waveTensorEquiv m (hilbertTmul (waveVacuum m) (waveVacuum m)) := by
    apply Lp.ext
    filter_upwards [polynomialGaussian_coeFn p, waveTensor_vacuum_coeFn m] with x hx hv
    simp only [waveTensorEquiv_apply, hx, hv, p, polynomialGaussianFun,
      MvPolynomial.eval_C]
  have hzero : polynomialLambda m p = 0 := by
    simp [polynomialLambda_eq, p]
  have hcore : p ∈ finiteFockPolynomialCore m := by
    rw [finiteFockPolynomialCore_eq_top]
    exact Submodule.mem_top
  have hg : (polynomialGaussian p, 0) ∈ (schrodingerLambda m).graph := by
    rw [schrodingerLambda_graph]
    apply (schrodingerFiniteFockGraph m).le_topologicalClosure
    have h : (polynomialGaussian p, polynomialGaussian (polynomialLambda m p)) ∈
        schrodingerFiniteFockGraph m := ⟨⟨p,hcore⟩,rfl⟩
    have hgz : polynomialGaussian (0 : MvPolynomial (Fin 2 × Fin m) ℂ) = 0 :=
      polynomialGaussianLinear.map_zero
    simpa only [hzero, hgz] using h
  obtain ⟨x,hx,hy⟩ := (schrodingerLambda m).mem_graph_iff.mp hg
  rw [← hp]
  exact (schrodingerLambda m).mem_ker_iff.mpr ⟨x,hx.symm,hy⟩

/-- The mean-zero test accepts the physical vacuum with certainty. -/
theorem schrodingerTensorP0_vacuum (m : ℕ) :
    schrodingerTensorP0 m (hilbertTmul (waveVacuum m) (waveVacuum m)) =
      hilbertTmul (waveVacuum m) (waveVacuum m) :=
  (schrodingerTensorP0_fixed_iff m _).mpr (waveTensor_vacuum_mem_kernel m)

/-- The forward vacuum-orbit implication of Proposition 6.1, including phases. -/
theorem schrodingerTensorP0_symplectic_vacuum {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (z : ℂ) :
    let ψ := z • waveSymplecticUnitary S hS (waveVacuum m)
    schrodingerTensorP0 m (hilbertTmul ψ ψ) = hilbertTmul ψ ψ := by
  dsimp only
  have h := waveSymplecticUnitary_tensorP0 S hS
    (hilbertTmul (waveVacuum m) (waveVacuum m))
  rw [schrodingerTensorP0_vacuum, diagonalWaveAction_tmul] at h
  simpa only [map_smul, smul_apply] using
    congrArg (fun v => z • (z • v)) h.symm

/-- The manuscript's `p₀(ψ)`: expectation of the actual closed-kernel
projection on two copies of the Schrödinger wavefunction. -/
def schrodingerMeanZeroAcceptance {m : ℕ} (ψ : WaveSpace m) : ℝ :=
  (hilbertTensorSquare (WaveSpace m)).accProbA (schrodingerTensorP0 m) ψ

/-- Identical one-copy unitaries commuting with copy rotations preserve the
acceptance probability of the physical closed-kernel test. -/
theorem CommutesWithCopyRotations.meanZeroAcceptance {m : ℕ}
    {U : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m} (hU : CommutesWithCopyRotations U)
    (ψ : WaveSpace m) :
    schrodingerMeanZeroAcceptance (U ψ) = schrodingerMeanZeroAcceptance ψ := by
  unfold schrodingerMeanZeroAcceptance TensorSquare.accProbA
  change (inner ℂ (hilbertTmul (U ψ) (U ψ))
    (schrodingerTensorP0 m (hilbertTmul (U ψ) (U ψ)))).re =
      (inner ℂ (hilbertTmul ψ ψ) (schrodingerTensorP0 m (hilbertTmul ψ ψ))).re
  have hP : schrodingerTensorP0 m (hilbertTmul (U ψ) (U ψ)) =
      hilbertTensorEquiv U U (schrodingerTensorP0 m (hilbertTmul ψ ψ)) := by
    simpa only [diagonalWaveAction_eq_tensorEquiv, hilbertTensorEquiv_tmul] using
      (hU.tensorP0 (hilbertTmul ψ ψ)).symm
  apply congrArg Complex.re
  refine (congrArg (inner ℂ (hilbertTmul (U ψ) (U ψ))) hP).trans ?_
  simpa only [hilbertTensorEquiv_tmul] using
    (hilbertTensorEquiv U U).inner_map_map (hilbertTmul ψ ψ)
      (schrodingerTensorP0 m (hilbertTmul ψ ψ))

/-- The acceptance invariance stated after manuscript Eq. (6.2):
`p₀(U_S ψ) = p₀(ψ)`, with no moment or normalization assumption on the input. -/
theorem schrodingerMeanZeroAcceptance_symplectic {m : ℕ}
    (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (ψ : WaveSpace m) :
    schrodingerMeanZeroAcceptance (waveSymplecticUnitary S hS ψ) =
      schrodingerMeanZeroAcceptance ψ :=
  (waveSymplecticUnitary_commutesWithCopyRotations S hS).meanZeroAcceptance ψ

/-- For a unit input, certainty is equivalent to the actual projection fixing
its tensor square. -/
theorem schrodingerMeanZeroAcceptance_eq_one_iff_fixed {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerMeanZeroAcceptance ψ = 1 ↔
      schrodingerTensorP0 m (hilbertTmul ψ ψ) = hilbertTmul ψ ψ := by
  have hn : ‖hilbertTmul ψ ψ‖ = 1 := by
    simpa only [hilbertTensorSquare, hψ, one_mul] using
      (hilbertTensorSquare (WaveSpace m)).norm_tp ψ ψ
  unfold schrodingerMeanZeroAcceptance TensorSquare.accProbA
  change (inner ℂ (hilbertTmul ψ ψ) (schrodingerTensorP0 m (hilbertTmul ψ ψ))).re = 1 ↔ _
  exact projection_expectation_one_iff (schrodingerTensorP0 m) (schrodingerTensorP0_symmetric m)
    (schrodingerTensorP0_idempotent m) (hilbertTmul ψ ψ) hn

/-- Certainty is equivalent to membership in the actual closed `Λ` kernel.
Kernel membership includes membership in the prescribed operator domain. -/
theorem schrodingerMeanZeroAcceptance_eq_one_iff_kernel {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerMeanZeroAcceptance ψ = 1 ↔
      waveTensorEquiv m (hilbertTmul ψ ψ) ∈ (schrodingerLambda m).ker :=
  (schrodingerMeanZeroAcceptance_eq_one_iff_fixed ψ hψ).trans
    (schrodingerTensorP0_fixed_iff m (hilbertTmul ψ ψ))

/-- Proposition 6.1's characteristic-function converse and vacuum-orbit
forward implication, in completed tensor coordinates. -/
theorem schrodingerTensorP0_fixed_iff_meanZeroGaussianWaveStates {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerTensorP0 m (hilbertTmul ψ ψ) = hilbertTmul ψ ψ ↔
      ψ ∈ meanZeroGaussianWaveStates m := by
  constructor
  · intro hfix
    obtain ⟨Q,hQcont,_,hχ⟩ := pureWaveCharacteristic_kernel_eq_exp_quadratic hψ hfix
    exact exists_symplectic_vacuum_of_pureCharacteristic_quadratic ψ hψ Q hQcont hχ
  · rintro ⟨S,hS,z,_,rfl⟩
    exact schrodingerTensorP0_symplectic_vacuum S hS z

/-- The manuscript's centered Gaussian state set is exactly the unit vectors
whose tensor square is annihilated by the actual closed generator. -/
theorem mem_meanZeroGaussianWaveStates_iff_kernel {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    ψ ∈ meanZeroGaussianWaveStates m ↔
      waveTensorEquiv m (hilbertTmul ψ ψ) ∈ (schrodingerLambda m).ker :=
  (schrodingerTensorP0_fixed_iff_meanZeroGaussianWaveStates ψ hψ).symm.trans
    (schrodingerTensorP0_fixed_iff m (hilbertTmul ψ ψ))

/-- The physical mean-zero test has certainty exactly on the independent
symplectic-vacuum characterization of the manuscript's Gaussian states. -/
theorem schrodingerMeanZeroAcceptance_eq_one_iff {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerMeanZeroAcceptance ψ = 1 ↔ ψ ∈ meanZeroGaussianWaveStates m :=
  (schrodingerMeanZeroAcceptance_eq_one_iff_fixed ψ hψ).trans
    (schrodingerTensorP0_fixed_iff_meanZeroGaussianWaveStates ψ hψ)

/-- **Proposition 6.1**, all three manuscript items, for the actual Schrödinger
Hilbert space: centered Gaussianity, `Λ ψ⊗² = 0`, and `p₀(ψ) = 1`.
The second item is expressed by closed-operator kernel membership, which
also records the required domain condition. -/
theorem bosonicMeanZeroGaussian_characterization {m : ℕ}
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    List.TFAE [ψ ∈ meanZeroGaussianWaveStates m,
      waveTensorEquiv m (hilbertTmul ψ ψ) ∈ (schrodingerLambda m).ker,
      schrodingerMeanZeroAcceptance ψ = 1] := by
  tfae_have 1 ↔ 2 := mem_meanZeroGaussianWaveStates_iff_kernel ψ hψ
  tfae_have 3 ↔ 2 := schrodingerMeanZeroAcceptance_eq_one_iff_kernel ψ hψ
  tfae_finish

end
end GaussianTesting
