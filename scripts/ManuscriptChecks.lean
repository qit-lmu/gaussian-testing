import GaussianTesting

/-!
# Manuscript comparison checks

Run `lake env lean scripts/ManuscriptChecks.lean` after `lake build`.
Each example applies a public theorem to its manuscript statement on a
general Hilbert space or in a concrete Gaussian model. The working manuscript is `material/manuscript.tex`.
In the robustness examples its acceptance deficit `τ` is named `ε` in Lean.
-/

namespace GaussianTesting

-- Kac preliminaries use normalized Euclidean surface measure on the actual two-sphere.
example : SO3.sphereMeasure Set.univ = 1 := SO3.sphereMeasure_univ

example (g : SO3.Group) :
    MeasureTheory.MeasurePreserving (SO3.sphereRotation g)
      SO3.sphereMeasure SO3.sphereMeasure :=
  SO3.sphereRotation_measurePreserving g

-- The point action is the ordinary matrix action in R³.
example (g : SO3.Group) (x : SO3.Sphere) (i : Fin 3) :
    (SO3.sphereRotation g x : SO3.SphereAmbient) i =
      ∑ j, g.val i j * (x : SO3.SphereAmbient) j :=
  SO3.rotationEquiv_apply g x i

-- The representation is inverse pullback, with the correct multiplication order.
example (g : SO3.Group) (f : SO3.SphereSpace) :
    (SO3.sphereRepresentation g f : SO3.Sphere → ℂ) =ᵐ[SO3.sphereMeasure]
      fun x => f (SO3.sphereRotation g⁻¹ x) :=
  SO3.sphereRotationAction_coeFn g f

example (g h : SO3.Group) (f : SO3.SphereSpace) :
    SO3.sphereRepresentation (g * h) f =
      SO3.sphereRepresentation g (SO3.sphereRepresentation h f) :=
  SO3.sphereRotationAction_mul g h f

example (g : SO3.Group) (f h : SO3.SphereSpace) :
    inner ℂ (SO3.sphereRepresentation g f) (SO3.sphereRepresentation g h) = inner ℂ f h :=
  (SO3.sphereRepresentation g).inner_map_map f h

example (f : SO3.SphereSpace) : Continuous (fun g => SO3.sphereRepresentation g f) :=
  SO3.continuous_sphereRepresentation_orbit f

-- A uniform circle average is the invariant-space projection on any Hilbert space.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : SO3.Group →* E ≃ₗᵢ[ℂ] E) (hπ : ∀ v : E, Continuous (fun g => π g v))
    (a : Fin 3) (v : E) :
    ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ in 0..2 * Real.pi, π (SO3.axisRotation a θ) v =
      (UnitaryRepresentation.fixedSubspace π (SO3.axisSubgroups a)).starProjection v :=
  SO3.axisCircleAverage_eq_fixedProjection π hπ a v

-- The Kac transition chooses an axis uniformly and then a uniform forward rotation.
example (f : C(SO3.Sphere, ℂ)) (x : SO3.Sphere) :
    SO3.sphereContinuousTransition f x = (3 : ℂ)⁻¹ •
      ∑ a : Fin 3, ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ θ in 0..2 * Real.pi, f (SO3.sphereRotation (SO3.axisRotation a θ) x) :=
  SO3.sphereContinuousTransition_apply f x

example : SO3.sphereKacTransition = SO3.kacAverage SO3.sphereRepresentation :=
  SO3.sphereKacTransition_eq_kacAverage

-- The pointwise continuous-observable formula determines the whole L² operator.
example (T : SO3.SphereSpace →L[ℂ] SO3.SphereSpace)
    (hT : ∀ f : C(SO3.Sphere, ℂ), T (SO3.sphereContinuousToLp f) =
      SO3.sphereContinuousToLp (SO3.sphereContinuousTransition f)) :
    T = SO3.kacAverage SO3.sphereRepresentation :=
  (SO3.sphereKacTransition_unique T hT).trans SO3.sphereKacTransition_eq_kacAverage

-- The general spectral theorem now applies to the concrete Kac transition.
example : spectrum ℂ SO3.sphereKacTransition ⊆
    Complex.ofReal '' Set.Icc 0 (7 / 12 : ℝ) ∪ {1} := by
  rw [SO3.sphereKacTransition_eq_kacAverage]
  exact SO3.kacAverage_spectrum_subset SO3.sphereRepresentation
    SO3.continuous_sphereRepresentation_orbit

-- In Theorem 4.1, the spherical eigenvalue-one space consists exactly of constants.
example (f : SO3.SphereSpace) :
    SO3.sphereKacTransition f = f ↔
      ∃ c : ℂ, (f : SO3.Sphere → ℂ) =ᵐ[SO3.sphereMeasure] fun _ => c :=
  SO3.sphereKacTransition_eq_self_iff_ae_constant f

example : Module.End.eigenspace SO3.sphereKacTransition.toLinearMap 1 =
    Submodule.span ℂ {SO3.sphereConstant 1} :=
  SO3.sphereKacTransition_fixedSpace

-- Theorem 4.1: the norm on the orthogonal complement of constants is exactly 7/12.
example (f : SO3.SphereSpace) (hf : f ∈ SO3.sphereConstantsᗮ) :
    ‖SO3.sphereKacTransition f‖ ≤ (7 / 12 : ℝ) * ‖f‖ :=
  SO3.sphereKacTransition_norm_le_on_orthogonal f hf

-- The three axial degree-four harmonics realize the manuscript's a₄ = 3/8 matrix.
example (a b : Fin 3) (hab : a ≠ b) :
    SO3.sphereAxisContinuousAverage b (SO3.sphereZonalFour a) =
      (3 / 8 : ℂ) • SO3.sphereZonalFour b := by
  simpa only [ite_eq_right hab] using SO3.sphereAxisContinuousAverage_zonalFour b a

example (a : Fin 3) :
    (SO3.zonalFourPolynomial a).IsHomogeneous 4 ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i
        (MvPolynomial.pderiv i (SO3.zonalFourPolynomial a))) = 0 :=
  ⟨SO3.zonalFourPolynomial_isHomogeneous a, SO3.zonalFourPolynomial_laplacian a⟩

example : ∃ f : SO3.sphereMeanZero, f ≠ 0 ∧
    SO3.sphereMeanZeroKac f = (7 / 12 : ℂ) • f :=
  ⟨SO3.sphereSpinFourVector, SO3.sphereSpinFourVector_ne_zero, SO3.sphereMeanZeroKac_spinFour⟩

example : IsGreatest {r : ℝ | (r : ℂ) ∈ spectrum ℂ SO3.sphereMeanZeroKac} (7 / 12) :=
  SO3.sphereMeanZeroKac_isGreatest_spectrum

example : 1 - ‖SO3.sphereMeanZeroKac‖ = 5 / 12 := SO3.sphereKac_spectralGap

-- The manuscript's K_ψ is an actual positive contraction on any Hilbert space.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : HilbertSquare E →L[ℂ] HilbertSquare E}
    (hP : (hilbertTensorSquare E).IsAcceptance P) {ψ : E} (hψ : ‖ψ‖ = 1) :
    ((hilbertTensorSquare E).contractionOperator P ψ).IsPositive ∧
      ‖(hilbertTensorSquare E).contractionOperator P ψ‖ ≤ 1 :=
  ⟨(hilbertTensorSquare E).contractionOperator_isPositive hP ψ,
    (hilbertTensorSquare E).norm_contractionOperator_le_one hP hψ⟩

-- Its first two operator moments are precisely the p and q of Eq. (3.5).
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : HilbertSquare E →L[ℂ] HilbertSquare E}
    (hP : (hilbertTensorSquare E).IsAcceptance P) (ψ : E) :
    let T := hilbertTensorSquare E
    inner ℂ ψ (T.contractionOperator P ψ ψ) = (T.accProbA P ψ : ℂ) ∧
      inner ℂ ψ ((T.contractionOperator P ψ ^ 2) ψ) = (T.qProbA P ψ : ℂ) :=
  ⟨(hilbertTensorSquare E).contractionOperator_first_moment hP ψ,
    (hilbertTensorSquare E).contractionOperator_second_moment hP ψ⟩

-- Criticality concerns the actual projective differential, with no dimension restriction.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : HilbertSquare E →L[ℂ] HilbertSquare E}
    (hP : (hilbertTensorSquare E).IsAcceptance P) {ψ : E} (hψ : ‖ψ‖ = 1) :
    fderiv ℝ (fun v : RayTangent ψ =>
      (hilbertTensorSquare E).rayAcceptance P (rayOfTangent ψ hψ v)) 0 = 0 ↔
      (hilbertTensorSquare E).contractionOperator P ψ ψ =
        ((hilbertTensorSquare E).accProbA P ψ : ℂ) • ψ :=
  contraction_criticalPoint_iff hP hψ

-- The manuscript's trace-norm identity holds in any Hilbert basis and dimension.
example {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    (1 / 2 : ℝ) * traceNorm b
      (InnerProductSpace.rankOne ℂ ψ ψ - InnerProductSpace.rankOne ℂ φ φ) =
      Real.sqrt (1 - ‖inner ℂ φ ψ‖ ^ 2) := by
  rw [← pureStateDifference, traceNorm_pureStateDifference b ψ φ hψ hφ,
    norm_inner_symm φ ψ]
  ring

-- The square-root zero case includes distinct vectors on the same ray.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ψ : E) (hψ : ‖ψ‖ = 1) : pureStateTraceDistance ψ (-ψ) = 0 := by
  rw [pureStateTraceDistance_eq_sqrt ψ (-ψ) hψ (by simpa using hψ)]
  simp [inner_self_eq_norm_sq_to_K, hψ]

-- Theorem 1.1's pointwise promise, written in the manuscript's inner-product order.
example {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hfar : ∀ φ ∈ fermionicGaussianStates m, ‖inner ℂ φ ψ‖ ^ 2 ≤ 1 - ε ^ 2) :
    1 - δ ≤ (fermionicTestProtocol ψ hψ ε δ).real
      (repeatedTestAccepts (testingRounds 8 ε δ))ᶜ := by
  apply ((fermionic_gaussian_testing ψ hψ hε hδ).2.1 ?_).2
  intro φ hφ
  simpa only [norm_inner_symm ψ φ] using hfar φ hφ

-- The trace-distance promise uses the same fermionic protocol and copy count.
example {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hfar : ∀ φ ∈ fermionicGaussianStates m, ε ≤ pureStateTraceDistance ψ φ) :
    1 - δ ≤ (fermionicTestProtocol ψ hψ ε δ).real
      (repeatedTestAccepts (testingRounds 8 ε δ))ᶜ :=
  ((fermionic_gaussian_testing_traceDistance ψ hψ hε hδ).2.1 hfar).2

-- General bosonic Gaussian states on the full, infinite-dimensional wave space.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hfar : ∀ φ ∈ gaussianWaveStates m, ε ≤ pureStateTraceDistance ψ φ) :
    1 - δ ≤ (bosonicTestProtocol .gaussian ψ hψ ε δ).real
      (repeatedTestAccepts (testingRounds 48 ε δ))ᶜ :=
  ((bosonic_gaussian_testing_traceDistance .gaussian ψ hψ hε hδ).2.1 hfar).2

-- Figure 1(a) is an operator identity for arbitrary two-copy inputs.
example (m : ℕ) (f : H2 (Qm m)) :
    (fermionicBellReadout m).symm
      (fermionicBellOutcomeProjection m (fermionicBellReadout m f)) = PF m f :=
  LinearMap.congr_fun (fermionicBellMeasurement_eq_PF m) f

example {m : ℕ} (ψ : HF m) :
    (inner ℂ (tp2 ψ ψ) (fermionicBellMeasurement m (tp2 ψ ψ))).re =
      accProb (PF m) ψ := fermionicBellMeasurement_acceptance ψ

-- Zero modes accept. A single odd-parity Bell pair has score two.
example : fermionicBellEigenvalue 0 ((fun _ => false), (fun _ => false)) = 0 := by decide
example : fermionicBellEigenvalue 1 ((fun _ => false), (fun _ => true)) = 2 := by decide

-- The second mode's Jordan-Wigner prefix reverses its contribution.
-- Omitting that prefix would incorrectly give four rather than zero here.
example : fermionicBellEigenvalue 2 ((fun _ => false), (fun _ => true)) = 0 := by decide
example : fermionicBellEigenvalue 2 ((fun k => k = 1), (fun _ => true)) = 4 := by decide

-- Corollary 5.3 uses the paper's independent class, epsilon and integer count.
example {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hfar : pureFidelity (fermionicGaussianStates m) ψ ^ 2 ≤ 1 - ε ^ 2) :
    1 - δ ≤ (fermionicTestProtocol ψ hψ ε δ).real
      (repeatedTestAccepts ⌈8 / ε ^ 2 * Real.log (1 / δ)⌉₊)ᶜ ∧
    (fermionicTestCopies ε δ : ℝ) ≤ 16 / ε ^ 2 * Real.log (1 / δ) + 2 :=
  ⟨((fermionic_testing ψ hψ hε hδ).2.1 hfar).2,
    (fermionic_testing ψ hψ hε hδ).2.2.2⟩

example (ψ : HF 0) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hG : ψ ∈ fermionicGaussianStates 0) :
    (fermionicTestProtocol ψ hψ ε δ).real (repeatedTestAccepts (testingRounds 8 ε δ)) = 1 :=
  (fermionic_testing ψ hψ hε hδ).1 hG

example (ε δ : ℝ) : fermionicTestCopies ε δ =
    2 * ⌈8 / ε ^ 2 * Real.log (1 / δ)⌉₊ := rfl

-- Theorem 5.2: independent Gaussian class and only the paper's hypotheses.
example {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ accProb (PF m) ψ) :
    1 - 8 * τ ≤ pureFidelity (fermionicGaussianStates m) ψ ^ 2 :=
  fermionic_fidelity ψ hψ hp

example (ψ : HF 0) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ accProb (PF 0) ψ) :
    ∃ φ ∈ fermionicGaussianStates 0, 1 - 8 * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 := by
  obtain ⟨φ, hφ, hbound, _⟩ := fermionic_fidelity_witness ψ hψ hp
  exact ⟨φ, hφ, hbound⟩

-- The constructed copy action is exactly the exterior-algebra second quantization.
example {m : ℕ} (R : SO3.Group) (x : ExteriorAlgebra ℂ (Fin (3 * m) → ℂ)) :
    fermionCopyRepresentation m R (fermionTripleEquiv m (fermionExteriorEquiv x)) =
      fermionTripleEquiv m (fermionExteriorEquiv
        (ExteriorAlgebra.map (fermionOneParticleRotation (fermionCopyModeRotation m R)) x)) := by
  rw [fermionCopyRepresentation_apply, LinearIsometryEquiv.symm_apply_apply]
  exact congrArg (fermionTripleEquiv m)
    (fermionSecondQuantization_eq_exterior_map (fermionCopyModeRotation m R) x)

-- The spectrum is that of the actual finite pair average, with no assumed gap.
example (m : ℕ) : spectrum ℂ (Sop (PF m)).toContinuousLinearMap ⊆
    Complex.ofReal '' Set.Icc 0 (7 / 12 : ℝ) ∪ {1} :=
  fermionic_spectrum_subset m


-- Lemma 5.1 uses the independently defined orbit union, with no parity hypothesis.
example {m : ℕ} (ψ : HF m) (hψ : ‖ψ‖ = 1) :
    (ψ ∈ fermionicGaussianStates m ↔ lambdaF m (tp2 ψ ψ) = 0) ∧
      (ψ ∈ fermionicGaussianStates m ↔ accProb (PF m) ψ = 1) :=
  ⟨fermionicGaussian_iff_lambdaF hψ, fermionicGaussian_iff_accProb hψ⟩

-- The same statement includes the zero-mode Hilbert space.
example (ψ : HF 0) (hψ : ‖ψ‖ = 1) :
    ψ ∈ fermionicGaussianStates 0 ↔ accProb (PF 0) ψ = 1 :=
  fermionicGaussian_iff_accProb hψ

-- The standard normal form used by the proof requires no state or saturation assumption.
example {m : ℕ} (A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ)
    (hA : ∀ a b, A b a = -A a b) :
    ∃ (R : FermionRotation m) (ν : Fin m → ℝ),
      Matrix.transpose R.val * A * R.val = skewBlockMatrix ν :=
  exists_specialOrthogonal_skewNormalForm A hA

-- Eq. (5.2) is a full two-copy operator identity, not only a tensor-square identity.
example {m : ℕ} {R : FermionRotation m} {U : HF m ≃ₗᵢ[ℂ] HF m}
    (hU : ImplementsMajoranaRotation R U) (f : H2 (Qm m)) :
    fermionPairAction U (lambdaF m (fermionPairAction U.symm f)) = lambdaF m f :=
  hU.lambdaF_conjugate f


-- Section 5 preliminaries: arbitrary SO(2m), with the manuscript's column convention.
example {m : ℕ} (R : FermionRotation m) (a : Fin m × Bool) (ψ : HF m) :
    gaussianImplementer R (maj a ((gaussianImplementer R).symm ψ)) =
      ∑ b, ((R : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) b a : ℂ) • maj b ψ :=
  gaussianImplementer_majorana R a ψ

-- Each parity sector is a single orbit, independently of the certainty criterion.
example {m : ℕ} (x : Qm m) (ψ : HF m) :
    ψ ∈ fermionicGaussianOrbit x ↔
      IsGaussian ψ ∧ parityOp ψ = occupationParity x • ψ :=
  mem_fermionicGaussianOrbit_iff x ψ

-- Corollary 6.8 uses the manuscript's epsilon and the physical class fidelity.
example (k : BosonicTestKind) {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hfar : pureFidelity (k.stateClass m) ψ ^ 2 ≤ 1 - ε ^ 2) :
    1 - δ ≤ (bosonicTestProtocol k ψ hψ ε δ).real
      (repeatedTestAccepts (testingRounds k.fidelityConstant ε δ))ᶜ :=
  ((bosonic_physical_testing k ψ hψ hε hδ).2.1 hfar).2

-- Figure 1(d) has exactly the Section 6 accepting operator on all inputs.
example (m : ℕ) : fourCopyNumberMeasurement m = schrodingerFourCopyProjection m :=
  fourCopyNumberMeasurement_eq_projection m

-- Its Born probability on four identical inputs is p(psi), Eq. (6.5).
example {m : ℕ} (ψ : WaveSpace m) :
    (inner ℂ (fourCopyInput ψ) (fourCopyNumberMeasurement m (fourCopyInput ψ))).re =
      schrodingerFourCopyAcceptance ψ := fourCopyNumberMeasurement_acceptance ψ

-- The basic consequence following Eq. (6.2) has no extra input hypotheses.
example {m : ℕ} (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ) (ψ : WaveSpace m) :
    schrodingerMeanZeroAcceptance (waveSymplecticUnitary S hS ψ) =
      schrodingerMeanZeroAcceptance ψ := schrodingerMeanZeroAcceptance_symplectic S hS ψ

-- Theorem 6.7 uses full reduced-operator covariance, not a supplied assumption.
example {m : ℕ} {κ : Type*} (b : HilbertBasis κ ℂ (WaveSpace m))
    (V : WaveSpace m ≃ₗᵢ[ℂ] WaveSpace m) (hV : CommutesWithCopyRotations V)
    (ψ : WaveSpace m) :
    schrodingerReducedState b (V ψ) =
      V.conjStarAlgEquiv (schrodingerReducedState b ψ) :=
  schrodingerReducedState_covariance b V hV ψ

-- Figure 1(b) identifies the physical equal-total-count readout with P0.
example (m : ℕ) : meanZeroNumberMeasurement m = schrodingerTensorP0 m :=
  meanZeroNumberMeasurement_eq_P0 m

-- Theorem 6.7 has the manuscript's physical class and only its hypotheses.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerFourCopyAcceptance ψ) :
    1 - 48 * τ ≤ pureFidelity (gaussianWaveStates m) ψ ^ 2 :=
  schrodinger_gaussian_fidelity ψ hψ hp

-- Theorem 6.4 has no supplied Kac-spectrum hypothesis on the physical wavefunction.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerMeanZeroAcceptance ψ) :
    1 - 8 * τ ≤ pureFidelity (meanZeroGaussianWaveStates m) ψ ^ 2 :=
  schrodinger_meanZero_fidelity ψ hψ hp

-- The witness and supremal-fidelity comparison concern the same physical state.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerMeanZeroAcceptance ψ) :
    ∃ φ ∈ meanZeroGaussianWaveStates m,
      1 - 8 * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 ∧
      ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity (meanZeroGaussianWaveStates m) ψ ^ 2 :=
  schrodinger_meanZero_fidelity_witness ψ hψ hp

-- Figure 1(c) uses the physical number readout.
example (m : ℕ) : coherentNumberMeasurement m = schrodingerQ m :=
  coherentNumberMeasurement_eq_Q m

-- Theorem 4.1 applies to arbitrary strongly continuous unitary SO(3) representations.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix.specialOrthogonalGroup (Fin 3) ℝ →* H ≃ₗᵢ[ℂ] H)
    (hπ : ∀ v : H, Continuous (fun g => π g v)) :
    spectrum ℂ (SO3.kacAverage π) ⊆ Complex.ofReal '' Set.Icc 0 (7 / 12 : ℝ) ∪ {1} :=
  SO3.kacAverage_spectrum_subset π hπ

-- Eq. (3.2) takes the supremum of absolute overlaps before squaring.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (G : Set E) (ψ : E) :
    pureFidelity G ψ = sSup ((fun φ => ‖inner ℂ ψ φ‖) '' G) := rfl

-- Eq. (3.4) identifies the gradient of ray acceptance in horizontal coordinates.
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : HilbertSquare H →L[ℂ] HilbertSquare H} (hP : (hilbertTensorSquare H).IsAcceptance P)

example {x : H} (hx : ‖x‖ = 1) :
    HasGradientAt (fun v : RayTangent x => (hilbertTensorSquare H).rayAcceptance P (rayOfTangent x hx v))
      (⟨(4 : ℂ) • ((hilbertTensorSquare H).KvecA P x - ((hilbertTensorSquare H).accProbA P x : ℂ) • x),
        (hilbertTensorSquare H).inner_gradAccA_eq_zero hP hx⟩ : RayTangent x) 0 :=
  fubiniStudyGradient_rayAcceptance hP hx

-- Test the metric pairing on an arbitrary horizontal variation at the initial ray.
example {x : H} (hx : ‖x‖ = 1) (v : RayTangent x) :
    fderiv ℝ (fun w : RayTangent x => (hilbertTensorSquare H).rayAcceptance P (rayOfTangent x hx w)) 0 v =
      (inner ℂ ((hilbertTensorSquare H).gradAccA P x) (v : H)).re := by
  exact (fubiniStudyGradient_rayAcceptance hP hx).fderiv_apply (y := v)

end

-- Lemma 3.1, local unit-vector solutions on the completed Hilbert tensor square.
section
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : HilbertSquare H →L[ℂ] HilbertSquare H} (hP : (hilbertTensorSquare H).IsAcceptance P)

example (x₀ : H) (hx₀ : ‖x₀‖ = 1) :
    ∃ δ > (0 : ℝ), ∃ γ : ℝ → H, γ 0 = x₀ ∧
      (hilbertTensorSquare H).IsUnitFlowOn P γ (Icc 0 δ) ∧ ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 δ) := by
  obtain ⟨δ, hδ, hflow⟩ := (hilbertTensorSquare H).exists_smooth_local_unitFlow hP
  exact ⟨δ, hδ, hflow x₀ hx₀⟩

-- Both curves can be defined arbitrarily outside their respective intervals.
-- They agree on their overlap, where integrated squared speed gives the gain in acceptance.
example {γ η : ℝ → H} {a b c : ℝ} (ha : a ≤ min b c) (hinit : γ a = η a)
    (hγ : (hilbertTensorSquare H).IsUnitFlowOn P γ (Icc a b))
    (hη : (hilbertTensorSquare H).IsUnitFlowOn P η (Icc a c)) :
    EqOn γ η (Icc a (min b c)) ∧
      (∫ t in a..min b c, ‖derivWithin γ (Icc a (min b c)) t‖ ^ 2) =
        (hilbertTensorSquare H).accProbA P (γ (min b c)) - (hilbertTensorSquare H).accProbA P (γ a) :=
  ⟨hγ.eqOn_overlap hη hP hinit,
    hγ.integral_norm_velocity_sq_eq hP ha (Icc_subset_Icc_right (min_le_left b c))⟩

-- The differential identity at the right endpoint uses the derivative within the interval.
example {γ : ℝ → H} {a b : ℝ} (hab : a ≤ b)
    (hγ : (hilbertTensorSquare H).IsUnitFlowOn P γ (Icc a b)) :
    HasDerivWithinAt (fun t => (hilbertTensorSquare H).accProbA P (γ t))
      (‖(hilbertTensorSquare H).gradAccA P (γ b)‖ ^ 2) (Icc a b) b :=
  hγ.hasDerivWithinAt_accProb hP (right_mem_Icc.mpr hab)

end

-- Lemma 3.1 on rays: the trajectory is smooth in every chart through its
-- current ray, and unique even among solutions given only by the chart ODE.
section
open Set Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {P : HilbertSquare H →L[ℂ] HilbertSquare H} (hP : (hilbertTensorSquare H).IsAcceptance P)

example (q : Projectivization ℂ H) :
    ∃ ρ : ℝ → Projectivization ℂ H, ρ 0 = q ∧
      (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0) ∧
      (∀ t ∈ Ici (0:ℝ), ∀ u : H, ρ t ∈ rayChartDomain u →
        ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun r => rayChart u (ρ r)) (Ici 0) t) ∧
      ∀ σ : ℝ → Projectivization ℂ H, σ 0 = q →
        (hilbertTensorSquare H).IsProjectiveFlowOn P σ (Ici 0) → EqOn σ ρ (Ici 0) :=
  projective_gradient_flow hP q

-- The intrinsic ODE yields a lift with any prescribed unit initial representative.
example {s : Set ℝ} {ρ : ℝ → Projectivization ℂ H}
    (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ s) {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ s) (x : H) (hx : ‖x‖ = 1)
    (hrep : ∀ hn : x ≠ 0, ρ a = Projectivization.mk ℂ x hn) :
    ∃ γ : ℝ → H, γ a = x ∧ (hilbertTensorSquare H).IsUnitFlowOn P γ (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ hn : γ t ≠ 0, ρ t = Projectivization.mk ℂ (γ t) hn :=
  hρ.exists_unit_lift_Icc hP hab hI x hx hrep

example {s : Set ℝ} {ρ : ℝ → Projectivization ℂ H}
    (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ s) {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ s) : dist (ρ a) (ρ b) ^ 2 ≤ b - a :=
  hρ.dist_sq_le_time_sub hP hab hI

example {a b : ℝ} {ρ : ℝ → Projectivization ℂ H}
    (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ico a b)) (hab : a < b) :
    ∃ q, Tendsto ρ (𝓝[<] b) (𝓝 q) ∧ ∃ c > b, ∃ η, EqOn ρ η (Ico a b) ∧
      η b = q ∧ (hilbertTensorSquare H).IsProjectiveFlowOn P η (Icc a c) :=
  hρ.continue_at_finite_time hP hab

end

-- Theorem 3.4: the angular estimate and every linear bound hold for the same state.
example {ι : Type*} [Fintype ι] {P : H2 ι →ₗ[ℂ] H2 ι}
    (hP : IsAcceptanceProjection P) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (gap : SpectralGapHyp P α) (hne : (certaintyStates (accProb P)).Nonempty)
    {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    ∃ φ ∈ certaintyStates (accProb P),
      (3 / 2 * α < accProb P ψ → Real.arccos ‖inner ℂ ψ φ‖ ≤
        Real.arcsin (Real.sqrt (Cgap α * (1 - accProb P ψ))) / 2) ∧
      ∀ τ ≥ (0 : ℝ), 1 - τ ≤ accProb P ψ →
        1 - Cgap α * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 := by
  obtain ⟨φ, hφ, _, hang, hlin, _⟩ := robust_testing_of_gap_sharp hP hα0 hα gap hne hψ
  exact ⟨φ, hφ, hang, hlin⟩

-- The class-fidelity angular bound on the Hilbert tensor square with moment data.
example {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : TensorSquare E K) {P : K →L[ℂ] K} (hP : T.IsAcceptance P) (hnorm : ‖P‖ ≤ 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (data : T.LojasiewiczData P α)
    (hne : (certaintyStates (T.accProbA P)).Nonempty) {ψ : E} (hψ : ‖ψ‖ = 1)
    (hhigh : 3 / 2 * α < T.accProbA P ψ) :
    Real.arccos (pureFidelity (certaintyStates (T.accProbA P)) ψ) ≤
      Real.arcsin (Real.sqrt (Cgap α * (1 - T.accProbA P ψ))) / 2 :=
  (T.robust_testing_abstract_sharp hP hnorm hα0 hα data hne hψ).angular_fidelity hhigh

-- Theorem 1.2, specialized to the finite gap hypothesis.
example {ι : Type*} [Fintype ι] {P : H2 ι →ₗ[ℂ] H2 ι}
    (hP : IsAcceptanceProjection P) {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (gap : SpectralGapHyp P α) (hne : (certaintyStates (accProb P)).Nonempty)
    {ψ : H ι} (hψ : ‖ψ‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) (hp : 1 - τ ≤ accProb P ψ) :
    1 - Cgap α * τ ≤ pureFidelity (certaintyStates (accProb P)) ψ ^ 2 :=
  testing_fidelity_of_gap hP hα0 hα gap hne hψ hτ hp

-- The spectral equivalence used in Lemma 3.3 on any complex Hilbert space.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H} (hS : 0 ≤ S) (hnorm : ‖S‖ ≤ 1) (α : ℝ) :
    (spectrum ℂ S ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1}) ↔
      0 ≤ (S - 1) * (S - algebraMap ℝ (H →L[ℂ] H) α) :=
  spectrum_gap_iff_polynomial_nonneg hS hnorm α

-- Lemmas 3.2 and 3.3 on the completed tensor cube of any complex Hilbert space.
section
open scoped InnerProductSpace
open Set Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {P : HilbertSquare H →L[ℂ] HilbertSquare H} (hP : (hilbertTensorSquare H).IsAcceptance P)

example {ψ : H} (hψ : ‖ψ‖ = 1) :
    let Ψ := hilbertTmul ψ (hilbertTmul ψ ψ)
    let S := threeCopyAverage P
    let p := (hilbertTensorSquare H).accProbA P ψ
    let q := (hilbertTensorSquare H).qProbA P ψ
    ⟪Ψ, S Ψ⟫_ℂ = (p : ℂ) ∧ ⟪Ψ, S (S Ψ)⟫_ℂ = (((p + 2 * q) / 3 : ℝ) : ℂ) :=
  threeCopyAverage_moments hP hψ

-- Following Lemma 3.2, the average fixes exactly the elementary cubes of certainty states.
example {ψ : H} (hψ : ‖ψ‖ = 1) :
    let Ψ := hilbertTmul ψ (hilbertTmul ψ ψ)
    threeCopyAverage P Ψ = Ψ ↔ (hilbertTensorSquare H).accProbA P ψ = 1 :=
  threeCopyAverage_fixed_iff_accProb_eq_one hP hψ

-- Nonempty certainty supplies an eigenvector attaining the upper endpoint.
example (hne : (certaintyStates ((hilbertTensorSquare H).accProbA P)).Nonempty) :
    Module.End.HasEigenvalue (threeCopyAverage P).toLinearMap (1 : ℂ) ∧
      IsGreatest {r : ℝ | Module.End.HasEigenvalue (threeCopyAverage P).toLinearMap (r : ℂ)} 1 :=
  ⟨threeCopyAverage_hasEigenvalue_one hP hne, threeCopyAverage_isGreatest_eigenvalue hP hne⟩

example {α : ℝ} (hα : α ∈ Set.Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    16 * ((hilbertTensorSquare H).accProbA P ψ - 3 / 2 * α) *
      (1 - (hilbertTensorSquare H).accProbA P ψ) ≤ ‖(hilbertTensorSquare H).gradAccA P ψ‖ ^ 2 :=
  norm_gradAcc_sq_ge_of_threeCopy_spectrum hP hα hspec hψ

-- The footnote before Lemma 3.3 requires the gap only on the symmetric tensor cube.
-- Invariance, positivity, and both moments are proved, rather than extra hypotheses.
example {α : ℝ} (hα : α ∈ Set.Icc 0 1)
    (hspec : spectrum ℂ (symmetricThreeCopyAverage hP) ⊆
      Complex.ofReal '' Set.Icc 0 α ∪ {1})
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    16 * ((hilbertTensorSquare H).accProbA P ψ - 3 / 2 * α) *
      (1 - (hilbertTensorSquare H).accProbA P ψ) ≤
      ‖(hilbertTensorSquare H).gradAccA P ψ‖ ^ 2 :=
  norm_gradAcc_sq_ge_of_symmetricThreeCopy_spectrum hP hα hspec hψ

-- Eq. (3.7) applies directly to any chart-defined forward ray solution.
example {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    let p := fun r => (hilbertTensorSquare H).rayAcceptance P (ρ r)
    let g₂ := (hilbertTensorSquare H).rayGradientNormSq P (ρ t)
    HasDerivWithinAt p g₂ (Ici 0) t ∧
      Tendsto (fun r => dist (ρ r) (ρ t) / |r - t|) (𝓝[Ici 0 \ {t}] t) (𝓝 (Real.sqrt g₂)) ∧
      16 * (p t - 3 / 2 * α) * (1 - p t) ≤ g₂ ∧
      16 * (p 0 - 3 / 2 * α) * (1 - p t) ≤ 16 * (p t - 3 / 2 * α) * (1 - p t) :=
  ray_flow_derivative_bounds hP hα hspec hρ ht

-- At the initial ray the derivative and the Fubini–Study speed limit are right-sided.
example {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0)) :
    let p := fun r => (hilbertTensorSquare H).rayAcceptance P (ρ r)
    let g₂ := (hilbertTensorSquare H).rayGradientNormSq P (ρ 0)
    HasDerivWithinAt p g₂ (Ici 0) 0 ∧
      Tendsto (fun r => dist (ρ r) (ρ 0) / |r|) (𝓝[>] 0) (𝓝 (Real.sqrt g₂)) := by
  obtain ⟨hd, hv, _, _⟩ := ray_flow_derivative_bounds hP hα hspec hρ (t := 0) le_rfl
  exact ⟨hd, by simpa only [sub_zero, Ici_sdiff_left] using hv⟩

-- The paragraph after Eq. (3.7), using the manuscript's alpha range.
-- Comparison with time zero verifies strict increase at the initial endpoint.
example {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1) :
    let p : ℝ → ℝ := fun t => (hilbertTensorSquare H).rayAcceptance P (ρ t)
    (∀ t > 0, p 0 < p t ∧ p t < 1) ∧ Tendsto p atTop (𝓝 1) := by
  obtain ⟨hbelow, hstrict, hlimit⟩ := ray_acceptance_strictly_increases_to_one hP
    (show α ∈ Icc 0 1 from ⟨hα0, hα.le.trans (by norm_num)⟩) hspec hρ hhigh hlow
  refine ⟨fun t ht => ⟨?_, hbelow t ht.le⟩, hlimit⟩
  exact hstrict (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht.le) ht

-- Theorem 3.4's path-length estimate gives a Cauchy trajectory and a normalized
-- certainty witness, with the displayed half-arcsine bound at the initial ray.
example {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0))
    (hlow : (hilbertTensorSquare H).rayAcceptance P (ρ 0) < 1) :
    Cauchy (map ρ atTop) ∧
      ∃ (φ : H) (hφ : φ ∈ certaintyStates ((hilbertTensorSquare H).accProbA P)),
        let q := Projectivization.mk ℂ φ (by intro h; simpa [h] using hφ.1)
        Tendsto ρ atTop (𝓝 q) ∧
          dist (ρ 0) q ≤
            Real.arcsin (Real.sqrt ((1 - (hilbertTensorSquare H).rayAcceptance P (ρ 0)) /
              (1 - 3 / 2 * α))) / 2 := by
  have hαI : α ∈ Icc 0 1 := ⟨hα0, hα.le.trans (by norm_num)⟩
  refine ⟨ray_trajectory_cauchy hP hαI hspec hρ hhigh hlow, ?_⟩
  obtain ⟨φ, hφ, hlimit, hbound⟩ :=
    ray_trajectory_tendsto_certaintyState hP hαI hspec hρ hhigh hlow
  exact ⟨φ, hφ, hlimit, hbound 0 le_rfl⟩

-- Theorem 3.4: high acceptance supplies the angular fidelity bound even without
-- an assumed certainty witness; the projective limit constructs one.
example {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ψ : H} (hψ : ‖ψ‖ = 1) (hhigh : 3 / 2 * α < (hilbertTensorSquare H).accProbA P ψ) :
    Real.arccos (pureFidelity (certaintyStates ((hilbertTensorSquare H).accProbA P)) ψ) ≤
      Real.arcsin (Real.sqrt (Cgap α * (1 - (hilbertTensorSquare H).accProbA P ψ))) / 2 :=
  angular_fidelity_of_threeCopy_spectrum hP hα0 hα hspec hψ hhigh

-- The same certainty state gives the angular estimate and the linear bound
-- for every error level, including the low-acceptance and certainty cases.
example {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    (hne : (certaintyStates ((hilbertTensorSquare H).accProbA P)).Nonempty)
    {ψ : H} (hψ : ‖ψ‖ = 1) :
    ∃ φ ∈ certaintyStates ((hilbertTensorSquare H).accProbA P),
      Real.arccos (pureFidelity (certaintyStates ((hilbertTensorSquare H).accProbA P)) ψ) ≤
        Real.arccos ‖inner ℂ ψ φ‖ ∧
      (3 / 2 * α < (hilbertTensorSquare H).accProbA P ψ →
        Real.arccos ‖inner ℂ ψ φ‖ ≤
          Real.arcsin (Real.sqrt (Cgap α * (1 - (hilbertTensorSquare H).accProbA P ψ))) / 2) ∧
      ∀ τ ≥ (0 : ℝ), 1 - τ ≤ (hilbertTensorSquare H).accProbA P ψ →
        1 - Cgap α * τ ≤ ‖inner ℂ ψ φ‖ ^ 2 ∧
          ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity (certaintyStates ((hilbertTensorSquare H).accProbA P)) ψ ^ 2 := by
  obtain ⟨φ, hφ, hfid, hang, hlin, hupper⟩ :=
    robustness_of_threeCopy_spectrum hP hα0 hα hspec hne hψ
  exact ⟨φ, hφ, hfid, hang, fun τ hτ hp => ⟨hlin τ hτ hp, hupper⟩⟩

-- Theorems 3.4 and 1.2 use the very same spectral inclusion.
example {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Set.Icc 0 α ∪ {1})
    (hne : (certaintyStates ((hilbertTensorSquare H).accProbA P)).Nonempty)
    {ψ : H} (hψ : ‖ψ‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) (hp : 1 - τ ≤ (hilbertTensorSquare H).accProbA P ψ) :
    1 - Cgap α * τ ≤ pureFidelity (certaintyStates ((hilbertTensorSquare H).accProbA P)) ψ ^ 2 :=
  testing_fidelity_of_threeCopy_spectrum hP hα0 hα hspec hne hψ hτ hp

end

-- Lemma 6.2 for every normalized summable family in Fock space.
-- Every positive trace-class operator of trace one has such a representation.
example {κ : Type*} {ρ : L2 κ →L[ℂ] L2 κ}
    (hρ : IsPositiveTraceClass ρ) (htrace : positiveTrace ρ = 1) :
    ∃ (g : κ → L2 κ) (hg : GramFam g),
      (∑' i, ‖g i‖ ^ 2) = 1 ∧ gramOp g hg = ρ :=
  (show IsDensityOperator ρ from ⟨hρ, htrace⟩).exists_normalized_gram_representation

-- Equivalently, start with trace one in any Hilbert basis and recover the
-- expansion of the operator on every vector, with no mixture given as input.
example {m : ℕ} {ι : Type*} {ρ : FockB m →L[ℂ] FockB m}
    (hρ : 0 ≤ ρ) (b : HilbertBasis ι ℂ (FockB m))
    (htrace : HasSum (fun i => (inner ℂ (b i) (ρ (b i))).re) 1) :
    ∃ (g : (Fin m → ℕ) → FockB m), GramFam g ∧ (∑' i, ‖g i‖ ^ 2) = 1 ∧
      ∀ x, ρ x = ∑' i, inner ℂ (g i) x • g i := by
  have hd := (isDensityOperator_iff_hasSum_diagonal ρ b).mpr ⟨hρ, htrace⟩
  obtain ⟨g, hg, hmass, hrep⟩ := hd.exists_normalized_gram_representation
  refine ⟨g, hg, hmass, fun x => ?_⟩
  rw [← hrep, gramOp_apply]

-- The full physical statement needs neither a supplied Gram representation nor
-- a Fock/Schrödinger isometry or an assumed rotation identity. The Hilbert bases
-- are arbitrary coordinates for the basis-independent traces.
example {m : ℕ} {κ ν : Type*} {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsDensityOperator b ρ) {τ : ℝ}
    (hp : 1 - τ ≤ (HilbertDensity.operatorTrace c
      (schrodingerDensityTensor m ρ * schrodingerP0 m)).re) :
    1 - 2 * τ ≤ ‖ρ‖ := purity_schrodinger c hρ hp

example {m : ℕ} {κ ν : Type*} {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsDensityOperator b ρ) :
    (HilbertDensity.operatorTrace c (schrodingerDensityTensor m ρ * schrodingerP0 m)).re ∈
      Set.Icc (0 : ℝ) 1 := schrodinger_acceptance_mem_Icc c hρ

-- The projector is defined from the actual graph closure on wavefunctions.
example (m : ℕ) : (schrodingerLambda m).graph =
    (schrodingerFiniteFockGraph m).topologicalClosure := schrodingerLambda_graph m

example (m : ℕ) (θ : ℝ) (f : SchrodingerSpace m) :
    schrodingerRotation m θ (schrodingerP0 m f) = schrodingerP0 m f :=
  schrodingerRotation_P0 m θ f

-- The manuscript's signed-swap equality is an equality of complex traces,
-- without a positivity or self-adjointness hypothesis on the rotation.
example {m : ℕ} {κ ν : Type*} {b : HilbertBasis κ ℂ (WaveSpace m)}
    (c : HilbertBasis ν ℂ (SchrodingerSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m}
    (hρ : HilbertDensity.IsPositiveTraceClass b ρ) :
    HilbertDensity.operatorTrace c
      ((schrodingerRotation m (Real.pi / 2)).toContinuousLinearEquiv.toContinuousLinearMap *
        schrodingerDensityTensor m ρ) =
      HilbertDensity.operatorTrace b
        ((waveParity m).toContinuousLinearEquiv.toContinuousLinearMap * (ρ * ρ)) :=
  schrodinger_signedSwap_trace c hρ

-- Section 6, the actual four-copy projection and the reduced-state trace
-- used in Proposition 6.3. No physical/Fock intertwining is supplied.
example {m : ℕ} {κ ν : Type*}
    (b : HilbertBasis κ ℂ (WaveSpace m))
    (c : HilbertBasis ν ℂ (SchrodingerSpace m)) (ψ : WaveSpace m) :
    inner ℂ (fourCopyInput ψ) (schrodingerFourCopyProjection m (fourCopyInput ψ)) =
      HilbertDensity.operatorTrace c
        (schrodingerP0 m * schrodingerDensityTensor m (schrodingerReducedState b ψ)) :=
  schrodingerFourCopyProjection_expectation_eq_reducedTrace b c ψ

example {m : ℕ} {κ : Type*} (b : HilbertBasis κ ℂ (WaveSpace m))
    (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    HilbertDensity.IsDensityOperator b (schrodingerReducedState b ψ) :=
  schrodingerReducedState_isDensityOperator b ψ hψ

-- Section 6's physical coherent projection, its swap symmetry, and its
-- actual vacuum reduced-state expectation.
example (m : ℕ) :
    (hilbertTensorSquare (WaveSpace m)).IsAcceptance (schrodingerQ m) :=
  schrodingerQ_isAcceptance m

example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerCoherentAcceptance ψ ∈ Set.Icc (0 : ℝ) 1 :=
  schrodingerCoherentAcceptance_mem_Icc ψ hψ

example {m : ℕ} {κ : Type*} (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) :
    inner ℂ (hilbertTmul ψ ψ) (schrodingerQ m (hilbertTmul ψ ψ)) =
      HilbertDensity.operatorTrace b (waveVacuumProjection m * schrodingerReducedState b ψ) :=
  schrodingerQ_expectation_eq_reducedTrace b ψ

-- Section 6 preliminaries: the Weyl definition is the actual wavefunction
-- action, with no assumed exponential, moment, or representation bridge.
example (m : ℕ) (q p : WaveConfig m) (f : WaveSpace m) :
    (weylOperator m (q, p) f : WaveConfig m → ℂ) =ᵐ[MeasureTheory.volume]
      fun x => Complex.exp (Complex.I *
        ((inner ℝ p x - inner ℝ p q / 2 : ℝ) : ℂ)) * f (x - q) :=
  weylOperator_coeFn m (q, p) f

example (m : ℕ) (r s : WavePhase m) (f : WaveSpace m) :
    weylOperator m r (weylOperator m s f) =
      Complex.exp (-Complex.I * (waveSymplectic r s : ℂ) / 2) •
        weylOperator m (r + s) f := weylOperator_mul m r s f

example (m : ℕ) :
    Continuous (fun p : WavePhase m × WaveSpace m => weylOperator m p.1 p.2) :=
  continuous_weylOperator_apply m

example {m : ℕ} {κ : Type*} (b : HilbertBasis κ ℂ (WaveSpace m))
    {ρ : WaveSpace m →L[ℂ] WaveSpace m} (hρ : HilbertDensity.IsDensityOperator b ρ) :
    waveCharacteristic b ρ 0 = 1 ∧
      (∀ r, ‖waveCharacteristic b ρ r‖ ≤ 1) ∧
      (∀ r, waveCharacteristic b ρ (-r) = star (waveCharacteristic b ρ r)) ∧
      Continuous (waveCharacteristic b ρ) :=
  ⟨waveCharacteristic_zero b hρ, norm_waveCharacteristic_le_one b hρ,
    waveCharacteristic_neg b hρ.toIsPositiveTraceClass,
    continuous_waveCharacteristic b hρ.toIsPositiveTraceClass⟩

-- Section 6 background: actual vacuum Fourier integral and displacement covariance.
example (m : ℕ) (r : WavePhase m) :
    inner ℂ (waveVacuum m) (weylOperator m r (waveVacuum m)) =
      (Real.exp (-(‖r.1‖ ^ 2 + ‖r.2‖ ^ 2) / 4) : ℂ) :=
  inner_waveVacuum_weylOperator m r

example (m : ℕ) (r s : WavePhase m) (v : HilbertSquare (WaveSpace m)) :
    schrodingerTensorRotation m (Real.pi / 4)
      (tensorWeylOperator m r s ((schrodingerTensorRotation m (Real.pi / 4)).symm v)) =
      tensorWeylOperator m ((Real.sqrt 2)⁻¹ • (r-s)) ((Real.sqrt 2)⁻¹ • (r+s)) v :=
  schrodingerTensorRotation_balanced_weyl m r s v

example (m t : ℕ) :
    Continuous (fun p : Matrix.specialOrthogonalGroup (Fin t) ℝ × CopiesWaveSpace m t =>
      schrodingerSpecialOrthogonalRepresentation m t p.1 p.2) :=
  continuous_schrodingerSpecialOrthogonalRepresentation_apply m t

-- Physical Theorem 6.5 uses the manuscript's displaced-vacuum class and
-- needs no separately supplied error-sign or spectral hypothesis.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) {τ : ℝ}
    (hp : 1 - τ ≤ schrodingerCoherentAcceptance ψ) :
    1 - 4 * τ ≤ pureFidelity (coherentWaveStates m) ψ ^ 2 :=
  schrodinger_coherent_fidelity ψ hψ hp

-- Draft Lemma 6.6 (`lem:S-spectrum-coherent-states`), full-space quadratic form.
example (m : ℕ) (F : L2 ((Fin m → ℕ) × (Fin m → ℕ) × (Fin m → ℕ))) :
    0 ≤ (inner ℂ F (Slp (QB_norm_le_one m) (Slp (QB_norm_le_one m) F)) -
      (1 + (1 / 2 : ℝ)) * inner ℂ F (Slp (QB_norm_le_one m) F) +
      (1 / 2 : ℝ) * inner ℂ F F).re :=
  coherent_polynomial_gap m F

-- Lemma 6.6 concerns the spectrum on the full three-copy space, for every mode count.
example (m : ℕ) : spectrum ℂ (Slp (QB_norm_le_one m)) ⊆
    Complex.ofReal '' Set.Icc 0 (1 / 2 : ℝ) ∪ {1} :=
  coherent_spectrum_subset m

-- Proposition 6.1: the actual physical kernel implies a centered Gaussian
-- characteristic function, without supplying a functional equation or moments.
example {m : ℕ} {ψ : WaveSpace m} (hn : ‖ψ‖ = 1)
    (hψ : schrodingerTensorP0 m (hilbertTmul ψ ψ) = hilbertTmul ψ ψ) :
    ∃ Q : QuadraticForm ℝ (WavePhase m), Continuous Q ∧ (∀ r, Q r ≤ 0) ∧
      (∀ r, pureWaveCharacteristic m ψ r = (Real.exp (Q r) : ℂ)) :=
  pureWaveCharacteristic_kernel_eq_exp_quadratic hn hψ

-- Complete Proposition 6.1: all three manuscript items for any unit physical
-- wavefunction, with the prescribed closed-operator domain in the kernel item.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    List.TFAE [ψ ∈ meanZeroGaussianWaveStates m,
      waveTensorEquiv m (hilbertTmul ψ ψ) ∈ (schrodingerLambda m).ker,
      schrodingerMeanZeroAcceptance ψ = 1] :=
  bosonicMeanZeroGaussian_characterization ψ hψ

-- Proposition 6.3: the coherent conclusion uses the manuscript's independent
-- displaced-vacuum definition on actual L², including the global phase.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    schrodingerCoherentAcceptance ψ = 1 ↔
      ∃ (a : WavePhase m) (z : ℂ), ‖z‖ = 1 ∧ ψ = z • weylOperator m a (waveVacuum m) :=
  schrodingerCoherentAcceptance_eq_one_iff ψ hψ

-- Complete Proposition 6.3 uses the actual physical accepting projections
-- and independently defined vacuum orbits, with only the unit-norm hypothesis.
example {m : ℕ} (ψ : WaveSpace m) (hψ : ‖ψ‖ = 1) :
    (ψ ∈ gaussianWaveStates m ↔ schrodingerFourCopyAcceptance ψ = 1) ∧
    (ψ ∈ coherentWaveStates m ↔ schrodingerCoherentAcceptance ψ = 1) :=
  bosonicGaussian_and_coherent_characterization ψ hψ

-- The prescribed closed generator, including its domain, transports through
-- the proved number basis; the kernel test uses that same identification.
example (m : ℕ) (f g : FockB2 m) :
    (fockPairSchrodingerEquiv m f, fockPairSchrodingerEquiv m g) ∈
        (schrodingerLambda m).graph ↔ (f,g) ∈ (closedLambdaB m).graph :=
  fockPairSchrodingerEquiv_mem_graph_iff m f g

example (m : ℕ) (f : FockB2 m) :
    fockPairSchrodingerEquiv m (P0B m f) =
      schrodingerP0 m (fockPairSchrodingerEquiv m f) :=
  fockPairSchrodingerEquiv_P0B m f

-- No supplied intertwining hypothesis is needed for the constructed U_S.
example {m : ℕ} (S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (hS : S ∈ Matrix.symplecticGroup (Fin m) ℝ)
    (r : WavePhase m) (f : WaveSpace m) :
    (waveSymplecticUnitary S hS).symm (weylOperator m r (waveSymplecticUnitary S hS f)) =
      weylOperator m (phaseMatrixAction S⁻¹ r) f :=
  waveSymplecticUnitary_conjugate_weyl S hS r f

end GaussianTesting

-- Lemma 6.6 now concerns the actual pair projections on the completed
-- Schrödinger tensor cube, including the zero-mode case.
example (m : ℕ) : spectrum ℂ (GaussianTesting.schrodingerCoherentAverage m) ⊆
    Complex.ofReal '' Set.Icc 0 (1 / 2 : ℝ) ∪ {1} :=
  GaussianTesting.schrodinger_coherent_spectrum_subset m

-- Check the proof route as well as its mathematical statement: Theorem 3.4
-- must use the projective certainty limit and the manuscript's half-angle step.
private partial def manuscriptProofDependencies (env : Lean.Environment)
    (pending : List Lean.Name) (seen : Lean.NameSet := {}) : Lean.NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then manuscriptProofDependencies env rest seen
    else
      let seen := seen.insert name
      let more := ((env.find? name).bind (fun info => info.value? (allowOpaque := true)))
        |>.map Lean.Expr.getUsedConstants |>.getD #[]
      let localNames := more.toList.filter fun n =>
        n.toString.startsWith "GaussianTesting." || n.toString.startsWith "_private.GaussianTesting."
      manuscriptProofDependencies env (localNames ++ rest) seen

run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.robustness_of_threeCopy_spectrum]
  for required in [
      `GaussianTesting.projective_gradient_flow,
      `GaussianTesting.ray_trajectory_tendsto_certaintyState,
      `GaussianTesting.ray_integral_speed_le_potential_sub,
      `GaussianTesting.bounds_of_angular_witness] do
    unless deps.contains required do
      throwError "Theorem 3.4 no longer uses the required projective proof step: {required}"
  for former in [
      `GaussianTesting.TensorSquare.angular_witness_abstract,
      `GaussianTesting.TensorSquare.robust_testing_abstract_sharp,
      `GaussianTesting.TensorSquare.exists_global_flowA] do
    if deps.contains former then
      throwError "Theorem 3.4 still uses the earlier unit-vector proof: {former}"

-- Theorem 6.7 uses the explicitly displayed reduced-state identities.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodinger_gaussian_fidelity]
  for required in [
      `GaussianTesting.schrodingerReducedState_top_eigenstate,
      `GaussianTesting.schrodinger_meanZero_fidelity_witness,
      `GaussianTesting.schrodingerReducedState_covariance,
      `GaussianTesting.schrodingerCoherentAcceptance_eq_vacuumExpectation,
      `GaussianTesting.schrodinger_coherent_fidelity_witness] do
    unless deps.contains required do
      throwError "Theorem 6.7 no longer uses the required manuscript proof step: {required}"

-- Lemma 6.2 must retain the manuscript's rotation/closed-kernel/signed-swap route.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.purity_schrodinger]
  for required in [
      `GaussianTesting.schrodingerFiniteFockGraph_hasDerivAt,
      `GaussianTesting.RotationGraphClosure.integrated_identity,
      `GaussianTesting.schrodingerRotation_P0,
      `GaussianTesting.schrodingerRotation_quarter_waveTensor,
      `GaussianTesting.HilbertDensity.signedSwap_trace,
      `GaussianTesting.HilbertDensity.signedSwap_trace_norm_le_purity,
      `GaussianTesting.HilbertDensity.IsDensityOperator.purity_le_norm] do
    unless deps.contains required do
      throwError "Lemma 6.2 no longer uses the required manuscript proof step: {required}"

-- The four-copy identity must use the constructed projection, physical
-- wavefunction equivalence, and proved partial trace of the retained factors.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodingerFourCopyProjection_expectation_eq_reducedTrace]
  for required in [
      `GaussianTesting.waveTensor_surjective,
      `GaussianTesting.fourCopyProjection,
      `GaussianTesting.hilbertReshuffle,
      `GaussianTesting.HilbertDensity.operatorTrace_mul_reducedRight,
      `GaussianTesting.HilbertDensity.reducedRight_reshuffle_square] do
    unless deps.contains required do
      throwError "The four-copy identity no longer uses the required construction: {required}"

run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodingerQ_isAcceptance]
  for required in [
      `GaussianTesting.waveVacuum_norm,
      `GaussianTesting.waveParity_vacuum,
      `GaussianTesting.schrodingerTensorRotation_balanced_swap] do
    unless deps.contains required do
      throwError "The coherent projection no longer uses the required physical identity: {required}"

-- Characteristic-function continuity must use the actual strongly continuous
-- wavefunction action and the proved trace-class Gram representation.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.continuous_waveCharacteristic]
  for required in [
      `GaussianTesting.weylOperator,
      `GaussianTesting.weylOperator_factorization,
      `GaussianTesting.continuous_waveTranslation,
      `GaussianTesting.continuous_waveModulation_apply,
      `GaussianTesting.HilbertDensity.IsPositiveTraceClass.exists_gram_representation] do
    unless deps.contains required do
      throwError "Characteristic-function continuity no longer uses the required foundation: {required}"

-- These physical exactness arguments must follow their manuscript proofs.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.bosonicMeanZeroGaussian_characterization]
  for required in [
      `GaussianTesting.pureWaveCharacteristic_kernel_eq_exp_quadratic,
      `GaussianTesting.exists_symplectic_vacuum_of_pureCharacteristic_quadratic,
      `GaussianTesting.schrodingerTensorP0_symplectic_vacuum,
      `GaussianTesting.projection_expectation_one_iff] do
    unless deps.contains required do
      throwError "Proposition 6.1 no longer uses the required physical proof step: {required}"

run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.pureWaveCharacteristic_kernel_eq_exp_quadratic]
  for required in [
      `GaussianTesting.pureWaveCharacteristic_balanced_of_kernel,
      `GaussianTesting.characteristic_rotation_positive,
      `GaussianTesting.characteristic_rotation_log_parallelogram,
      `GaussianTesting.exists_bilinear_of_continuous_parallelogram] do
    unless deps.contains required do
      throwError "Proposition 6.1 no longer uses the required characteristic-function step: {required}"

run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodingerCoherentAcceptance_eq_one_iff]
  for required in [
      `GaussianTesting.coherent_factorization_of_acceptance_one,
      `GaussianTesting.coherent_factorization_normalized_character,
      `GaussianTesting.continuous_character_eq_exp_linear,
      `GaussianTesting.exists_waveSymplectic_eq_linear,
      `GaussianTesting.rankOne_eq_of_pureWaveCharacteristic_eq,
      `GaussianTesting.displaced_vacuum_factorization] do
    unless deps.contains required do
      throwError "Proposition 6.3 no longer uses the required coherent proof step: {required}"

-- The Gaussian half must use the manuscript's exact purity reduction, not
-- specialize a robustness theorem.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodingerFourCopyAcceptance_eq_one_iff]
  for required in [
      `GaussianTesting.schrodingerFourCopyAcceptance_eq_reducedTrace,
      `GaussianTesting.purity_schrodinger,
      `GaussianTesting.HilbertDensity.IsDensityOperator.exists_rankOne_of_norm_eq_one,
      `GaussianTesting.HilbertDensity.exists_unit_tmul_of_reducedRight_eq_rankOne,
      `GaussianTesting.schrodingerMeanZeroAcceptance_eq_one_iff,
      `GaussianTesting.mem_gaussianWaveStates_of_meanZero_factorization,
      `GaussianTesting.waveSymplecticUnitary_commutesWithCopyRotations,
      `GaussianTesting.waveSymplecticUnitary_weyl,
      `GaussianTesting.schrodingerCoherentAcceptance_eq_one_iff,
      `GaussianTesting.displaced_meanZeroGaussian_factorization] do
    unless deps.contains required do
      throwError "Proposition 6.3 no longer uses the required Gaussian proof step: {required}"

run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.fockPairSchrodingerEquiv_P0B]
  for required in [
      `GaussianTesting.orthonormal_schrodingerNumberVector,
      `GaussianTesting.dense_span_schrodingerNumberVector,
      `GaussianTesting.fockPairGraphEquiv_finiteGraph,
      `GaussianTesting.fockPairGraphEquiv_closedGraph] do
    unless deps.contains required do
      throwError "Kernel transport no longer uses the required physical identification: {required}"

run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodingerTensorP0_symplectic_vacuum]
  for required in [
      `GaussianTesting.waveTensor_vacuum_mem_kernel,
      `GaussianTesting.waveSymplecticUnitary_tensorP0,
      `GaussianTesting.schrodingerLambda_mem_kernel_iff_rotation_fixed,
      `GaussianTesting.symplectic_decomposition] do
    unless deps.contains required do
      throwError "Proposition 6.1 forward proof no longer uses the required construction: {required}"

run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodinger_coherent_spectrum_subset]
  for required in [
      `GaussianTesting.waveNumberCoordinates_conj_Q,
      `GaussianTesting.fockPairSchrodingerEquiv_ULp,
      `GaussianTesting.waveNumberCoordinates_rotation_symm,
      `GaussianTesting.orthonormal_schrodingerNumberVector,
      `GaussianTesting.dense_span_schrodingerNumberVector,
      `GaussianTesting.coherent_spectrum_subset] do
    unless deps.contains required do
      throwError "Physical Lemma 6.6 no longer uses its proved coordinate identification: {required}"

-- Theorem 6.5 follows the manuscript's direct application of Theorem 3.4
-- to physical Lemma 6.6 and the coherent equivalence of Proposition 6.3.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.schrodinger_coherent_fidelity]
  for required in [
      `GaussianTesting.robustness_of_threeCopy_spectrum,
      `GaussianTesting.schrodinger_coherent_spectrum_subset,
      `GaussianTesting.schrodingerQ_isAcceptance,
      `GaussianTesting.coherentWaveStates_eq_certaintyStates,
      `GaussianTesting.schrodingerCoherentAcceptance_eq_one_iff] do
    unless deps.contains required do
      throwError "Theorem 6.5 no longer uses the required physical proof step: {required}"

-- The Gaussian orbit identification is background, so it must not use the
-- paper's certainty or robustness theorems to characterize its own state class.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.mem_fermionicGaussianOrbit_iff,
     `GaussianTesting.fermionicGaussianStates_eq_isGaussian]
  for required in [
      `GaussianTesting.specialOrthogonal_induction,
      `GaussianTesting.exists_planeUnitary_implements_planeRotation,
      `GaussianTesting.exists_scalar_of_commutes_maj,
      `GaussianTesting.exists_planeUnitary_basis_of_parity_eq] do
    unless deps.contains required do
      throwError "Fermionic orbit identification no longer uses its background construction: {required}"
  for forbidden in [
      `GaussianTesting.IsGaussian.lambdaF_eq_zero,
      `GaussianTesting.fermionicGaussian_of_lambdaF_eq_zero,
      `GaussianTesting.fermionicGaussian_iff_lambdaF,
      `GaussianTesting.fermionicGaussian_iff_accProb,
      `GaussianTesting.fermionic_fidelity] do
    if deps.contains forbidden then
      throwError "Fermionic preliminaries depend on a manuscript result: {forbidden}"

-- Lemma 5.1 must retain the paper's general normal-form and occupation argument.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.fermionicGaussian_iff_lambdaF,
     `GaussianTesting.fermionicGaussian_iff_accProb]
  for required in [
      `GaussianTesting.exists_specialOrthogonal_skewNormalForm,
      `GaussianTesting.gaussianImplementer_implements,
      `GaussianTesting.ImplementsMajoranaRotation.covMat_symm,
      `GaussianTesting.ImplementsMajoranaRotation.sum_sq_covMat_symm,
      `GaussianTesting.norm_lambdaF_tp2,
      `GaussianTesting.abs_covMat_pair_le_one,
      `GaussianTesting.covMat_pair_signs_of_sum_eq,
      `GaussianTesting.nOp_eigen_of_expectation,
      `GaussianTesting.joint_eigen_basis,
      `GaussianTesting.ImplementsMajoranaRotation.lambdaF_tp2,
      `GaussianTesting.lambdaF_tp2_single,
      `GaussianTesting.accProb_PF_eq_one_iff] do
    unless deps.contains required do
      throwError "Lemma 5.1 no longer uses its manuscript proof step: {required}"
  if deps.contains `GaussianTesting.IsGaussian.lambdaF_eq_zero then
    throwError "Independent Lemma 5.1 uses the coordinate Gaussianity implication"

-- Theorem 5.2 follows the actual Γ∧ copy action, Theorem 4.1 and the
-- completed-tensor/projective-flow proof of Theorem 3.4.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.fermionic_fidelity]
  for required in [
      `GaussianTesting.fermionCopyRepresentation,
      `GaussianTesting.fermionSecondQuantization,
      `GaussianTesting.fermionTripleEquiv_majorana,
      `GaussianTesting.fermion_copyRepresentation_axis_derivatives,
      `GaussianTesting.fermion_copyRepresentation_axis_fixed,
      `GaussianTesting.fermion_Sop_eq_kacAverage,
      `GaussianTesting.SO3.kacAverage_spectrum_subset,
      `GaussianTesting.finite_robustness_of_spectrum,
      `GaussianTesting.finiteHilbert_average_spectrum,
      `GaussianTesting.robustness_of_threeCopy_spectrum,
      `GaussianTesting.ray_trajectory_tendsto_certaintyState,
      `GaussianTesting.fermionicGaussian_iff_accProb] do
    unless deps.contains required do
      throwError "Theorem 5.2 no longer uses its manuscript proof step: {required}"
  for forbidden in [
      `GaussianTesting.robust_testing_of_gap,
      `GaussianTesting.angular_witness_of_gap] do
    if deps.contains forbidden then
      throwError "Theorem 5.2 uses the former coordinate proof route: {forbidden}"

-- Corollary 5.3 uses Lemma 5.1, Theorem 5.2, and the independent repetition law.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.fermionic_testing]
  for required in [
      `GaussianTesting.fermionicGaussian_iff_accProb,
      `GaussianTesting.fermionic_fidelity,
      `GaussianTesting.fermionic_acceptance_le_of_far,
      `GaussianTesting.repeatedTestLaw,
      `GaussianTesting.repeatedTest_acceptance,
      `GaussianTesting.repeatedTest_rejection,
      `GaussianTesting.repeatedTest_soundness,
      `GaussianTesting.testingRounds_sufficient,
      `GaussianTesting.testingCopies_le] do
    unless deps.contains required do
      throwError "Corollary 5.3 no longer uses its manuscript proof step: {required}"

-- Figure 1(a) obtains PF by explicit Bell diagonalization, independently of Gaussianity.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.fermionicBellMeasurement_eq_PF]
  for required in [
      `GaussianTesting.fermionicBellVector_orthonormal,
      `GaussianTesting.fermionicBellReadout,
      `GaussianTesting.fermionicBellEigenvalue,
      `GaussianTesting.majoranaPair_fermionicBellVector,
      `GaussianTesting.lambdaF_fermionicBellBasis,
      `GaussianTesting.lambdaF_isSymmetric] do
    unless deps.contains required do
      throwError "Figure 1(a) no longer uses its explicit Bell readout: {required}"
  for forbidden in [
      `GaussianTesting.fermionicGaussian_iff_lambdaF,
      `GaussianTesting.fermionic_fidelity,
      `GaussianTesting.fermionic_testing] do
    if deps.contains forbidden then
      throwError "Figure 1(a) unexpectedly depends on a Gaussian testing theorem: {forbidden}"

-- The distance is defined through the trace of the operator modulus.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.pureStateTraceDistance]
  for required in [`GaussianTesting.traceNorm, `GaussianTesting.HilbertDensity.positiveTrace,
      `GaussianTesting.pureStateDifference] do
    unless deps.contains required do
      throwError "Pure-state trace distance no longer uses its operator definition: {required}"
  -- The recursive checker above follows only declarations in this repository.
  let info ← Lean.getConstInfo `GaussianTesting.traceNorm
  let names := (info.value? (allowOpaque := true)).map Lean.Expr.getUsedConstants |>.getD #[]
  unless names.contains `CFC.abs do
    throwError "The trace-norm definition no longer takes the positive operator modulus"

-- Both trace-distance endpoints retain the paper's repetition proof and trace identity.
run_elab do
  for (endpoint, corollary) in [
      (`GaussianTesting.fermionic_gaussian_testing_traceDistance, `GaussianTesting.fermionic_testing),
      (`GaussianTesting.bosonic_gaussian_testing_traceDistance, `GaussianTesting.bosonic_physical_testing)] do
    let deps := manuscriptProofDependencies (← Lean.getEnv) [endpoint]
    for required in [corollary,
        `GaussianTesting.pureFidelity_sq_le_iff,
        `GaussianTesting.le_pureStateTraceDistance_iff,
        `GaussianTesting.traceNorm_pureStateDifference,
        `GaussianTesting.abs_pureStateDifference,
        `GaussianTesting.pureStateDifference_cube,
        `GaussianTesting.repeatedTestLaw] do
      unless deps.contains required do
        throwError "Theorem 1.1 no longer uses its manuscript proof step: {required}"

-- The critical-point statement uses the projective gradient and the actual compression.
run_elab do
  let deps := manuscriptProofDependencies (← Lean.getEnv)
    [`GaussianTesting.contraction_criticalPoint_iff]
  for required in [
      `GaussianTesting.TensorSquare.contractionOperator,
      `GaussianTesting.TensorSquare.contractionOperator_apply,
      `GaussianTesting.TensorSquare.isFubiniStudyGradient_iff,
      `GaussianTesting.TensorSquare.gradAccA_eq_zero_iff_contractionOperator] do
    unless deps.contains required do
      throwError "The contraction critical-point theorem no longer uses its manuscript proof: {required}"

-- The cited fermionic span uses both Gaussian parity orbits and the full kernel.
example (m : ℕ) :
    Submodule.span ℂ ((fun ψ => GaussianTesting.tp2 ψ ψ) ''
      GaussianTesting.fermionicGaussianStates m) =
    LinearMap.ker (GaussianTesting.lambdaF m) :=
  GaussianTesting.fermionicGaussianSquareSpan_eq_kernel m

example (m : ℕ) (f : GaussianTesting.H2 (GaussianTesting.Qm m)) :
    GaussianTesting.swap2 (GaussianTesting.PF m f) = GaussianTesting.PF m f :=
  GaussianTesting.swap2_PF m f

example (m : ℕ) {A : GaussianTesting.H2 (GaussianTesting.Qm m) →L[ℂ]
      GaussianTesting.H2 (GaussianTesting.Qm m)}
    (hA : 0 ≤ A) (hn : ‖A‖ ≤ 1)
    (hc : ∀ ψ ∈ GaussianTesting.fermionicGaussianStates m,
      (inner ℂ (GaussianTesting.tp2 ψ ψ) (A (GaussianTesting.tp2 ψ ψ))).re = 1)
    (y : GaussianTesting.H2 (GaussianTesting.Qm m)) :
    (inner ℂ y (GaussianTesting.PF m y)).re ≤ (inner ℂ y (A y)).re :=
  GaussianTesting.fermionicTest_acceptance_le m hA hn hc y

namespace GaussianTesting

example (j : ℕ) : spinOverlap j =
    (∑ k ∈ Finset.range (j + 1), (-1 : ℝ)^k * (j.choose k : ℝ)^2) / 2^j := rfl

example : spinKacMaximum 2 = 1/2 := spinKacMaximum_two
example : spinKacMaximum 4 = 7/12 := spinKacMaximum_four
example {j : ℕ} (hj : 6 ≤ j) : spinKacMaximum j < 7/12 :=
  spinKacMaximum_lt_of_six_le hj

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2*j+1) {μ : ℂ} (hμ : μ ≠ 0) :
    μ ∈ spectrum ℂ (kacT J) ↔
      μ = (((1+2*spinOverlap j)/3 : ℝ) : ℂ) ∨ μ = (((1-spinOverlap j)/3 : ℝ) : ℂ) :=
  AngularMomentum.kacT_mem_spectrum_iff_of_integer_spin J hJ hn hμ

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2*j+1) :
    IsGreatest {r : ℝ | Module.End.HasEigenvalue (kacT J) (r : ℂ)} (spinKacMaximum j) :=
  AngularMomentum.kacT_isGreatest_eigenvalue_of_integer_spin J hJ hn

example : coherentSectorMaxEigenvalue 0 = 1 := coherentSectorMaxEigenvalue_zero
example : coherentSectorMaxEigenvalue 1 = 1/2 := coherentSectorMaxEigenvalue_one
example : coherentSectorMaxEigenvalue 2 = 1/2 := coherentSectorMaxEigenvalue_two
example {k : ℕ} (hk : 3 ≤ k) : coherentSectorMaxEigenvalue k < 1/2 :=
  coherentSectorMaxEigenvalue_lt_half hk



-- Standalone manuscript interfaces and global first-moment scope.
example (m : ℕ) : (parityOp : Module.End ℂ (HF m)) =
    (-Complex.I)^m • orderedMajoranaProduct m := parityOp_eq_majoranaProduct

example {m : ℕ} (a : Fin 2) (b : Fin m × Bool) (ψ : HF (2*m)) :
    fermionPairEquiv m (maj (fermionPairCopyMode a b.1, b.2) ψ) =
      fermionPairMajorana a b (fermionPairEquiv m ψ) :=
  fermionPairEquiv_majorana a b ψ

example (m : ℕ) : fermionPairL m =
    (-Complex.I) • (opL (parityOp (m := m)) ∘ₗ lambdaF m) := fermionPairL_eq

example (m : ℕ) : LinearMap.ker (fermionPairL m) = LinearMap.ker (lambdaF m) :=
  ker_fermionPairL

example {m : ℕ} (v : H2 (Qm m)) :
    HasDerivAt (fun θ => fermionPairRepresentation m (fermionPairCircle θ) v)
      ((Complex.I/2) • fermionPairL m v) 0 := fermionPairRepresentation_hasDerivAt v

example {m : ℕ} (v : H2 (Qm m)) :
    (∀ R, fermionPairRepresentation m R v = v) ↔ lambdaF m v = 0 :=
  fermionPairRepresentation_fixed_iff v

example (m : ℕ) : PF m =
    (UnitaryRepresentation.fixedSubspace (fermionPairRepresentation m) ⊤).starProjection.toLinearMap :=
  PF_eq_pairRotation_fixedProjection

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ E) (x : E) :
    HilbertDensity.IsDensityOperator b (InnerProductSpace.rankOne ℂ x x) ↔ ‖x‖ = 1 :=
  HilbertDensity.isDensityOperator_rankOne_iff b x

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} {b : HilbertBasis ι ℂ E} {ρ : E →L[ℂ] E}
    (hρ : HilbertDensity.IsDensityOperator b ρ) (hi : ρ * ρ = ρ) :
    ∃! q : Projectivization ℂ E, HilbertDensity.rayProjector q = ρ :=
  hρ.existsUnique_rayProjector hi

example {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m) (k : Fin m)
    (hx : MeasureTheory.Integrable (fun x : WaveConfig m =>
      x k * schrodingerDifferenceDensity b ψ x) MeasureTheory.volume)
    (hp : MeasureTheory.Integrable (fun x : WaveConfig m =>
      (2 * Real.pi * x k) * schrodingerDifferenceFourierDensity b ψ x) MeasureTheory.volume) :
    (∫ x : WaveConfig m, x k * schrodingerDifferenceDensity b ψ x) = 0 ∧
    (∫ x : WaveConfig m, (2 * Real.pi * x k) * schrodingerDifferenceFourierDensity b ψ x) = 0 :=
  schrodingerReducedState_globalFirstMoments b ψ k hx hp

example {m : ℕ} {κ : Type*} [Countable κ]
    (b : HilbertBasis κ ℂ (WaveSpace m)) (ψ : WaveSpace m)
    (s : Set (WaveConfig m)) (hs : MeasurableSet s) :
    (HilbertDensity.operatorTrace b (wavePositionEvent s hs * schrodingerReducedState b ψ)).re =
      ∫ x in s, schrodingerDifferenceDensity b ψ x :=
  schrodingerDifferenceDensity_positionEvent b ψ s hs

end GaussianTesting

namespace GaussianTesting

-- The full physical closed span, with precisely the manuscript's symmetry restriction.
example (m : ℕ) :
    (Submodule.span ℂ ((fun ψ => waveTensorEquiv m (hilbertTmul ψ ψ)) ''
      meanZeroGaussianWaveStates m)).topologicalClosure =
    (schrodingerLambda m).ker ⊓
      ((schrodingerCopySwap m).toContinuousLinearMap -
        ContinuousLinearMap.id ℂ (SchrodingerSpace m)).ker :=
  meanZeroGaussianSquareSpan_eq_symmetric_kernel m

example (f : SchrodingerSpace 0) :
    f ∈ meanZeroGaussianSquareSpan 0 ↔
      f ∈ (schrodingerLambda 0).ker ∧ schrodingerCopySwap 0 f = f :=
  mem_meanZeroGaussianSquareSpan_iff 0 f

-- No symmetry condition on A or span-identification assumption is supplied.
example (m : ℕ)
    (A : HilbertSquare (WaveSpace m) →L[ℂ] HilbertSquare (WaveSpace m))
    (hA : 0 ≤ A) (hn : ‖A‖ ≤ 1)
    (hc : ∀ φ ∈ meanZeroGaussianWaveStates m,
      (inner ℂ (hilbertTmul φ φ) (A (hilbertTmul φ φ))).re = 1)
    (ψ : WaveSpace m) : schrodingerMeanZeroAcceptance ψ ≤
      (inner ℂ (hilbertTmul ψ ψ) (A (hilbertTmul ψ ψ))).re :=
  bosonicMeanZeroGaussian_optimality m A hA hn hc ψ

end GaussianTesting
