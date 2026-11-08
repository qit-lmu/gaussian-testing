import GaussianTesting

-- Kac preliminaries: normalized surface measure and the actual L² rotation action.

/-- info: 'GaussianTesting.SO3.sphereMeasure_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereMeasure_univ

/-- info: 'GaussianTesting.SO3.continuous_sphereRotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.continuous_sphereRotation

/-- info: 'GaussianTesting.SO3.sphereRotation_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereRotation_measurePreserving

/-- info: 'GaussianTesting.SO3.sphereRotationAction_coeFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereRotationAction_coeFn

/-- info: 'GaussianTesting.SO3.sphereRotationAction_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereRotationAction_mul

/-- info: 'GaussianTesting.SO3.continuous_sphereRepresentation_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.continuous_sphereRepresentation_orbit

-- Kac preliminaries: uniform circle projections and the spherical transition formula.

/-- info: 'GaussianTesting.SO3.axisCircleAverage_eq_fixedProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.axisCircleAverage_eq_fixedProjection

/-- info: 'GaussianTesting.SO3.axisCircleAverageCLM_eq_fixedProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.axisCircleAverageCLM_eq_fixedProjection

/-- info: 'GaussianTesting.SO3.sphereAxisContinuousAverage_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereAxisContinuousAverage_apply

/-- info: 'GaussianTesting.SO3.sphereContinuousTransition_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereContinuousTransition_apply

/-- info: 'GaussianTesting.SO3.sphereContinuousToLp_denseRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereContinuousToLp_denseRange

/-- info: 'GaussianTesting.SO3.sphereKacTransition_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_apply

/-- info: 'GaussianTesting.SO3.sphereKacTransition_eq_kacAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_eq_kacAverage

/-- info: 'GaussianTesting.SO3.sphereKacTransition_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_continuous

/-- info: 'GaussianTesting.SO3.sphereKacTransition_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_unique

-- Theorem 4.1: the spherical fixed space consists exactly of constants.

/-- info: 'GaussianTesting.UnitaryRepresentation.groupKacAverage_eq_self_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.UnitaryRepresentation.groupKacAverage_eq_self_iff

/-- info: 'GaussianTesting.SO3.kacAverage_eq_self_iff_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.kacAverage_eq_self_iff_invariant

/-- info: 'GaussianTesting.SO3.sphereRotation_transitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereRotation_transitive

/-- info: 'GaussianTesting.SO3.sphereRepresentation_invariant_iff_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereRepresentation_invariant_iff_constant

/-- info: 'GaussianTesting.SO3.sphereKacTransition_eq_self_iff_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_eq_self_iff_constant

/-- info: 'GaussianTesting.SO3.sphereKacTransition_eq_self_iff_ae_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_eq_self_iff_ae_constant

/-- info: 'GaussianTesting.SO3.sphereKacTransition_fixedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_fixedSpace

-- Theorem 4.1: upper bound, spin-four attainment, and exact spherical gap.

/-- info: 'GaussianTesting.SO3.sphereMeanZeroKac_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereMeanZeroKac_norm_le

/-- info: 'GaussianTesting.SO3.sphereKacTransition_quadratic_le_on_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_quadratic_le_on_orthogonal

/-- info: 'GaussianTesting.SO3.sphereContinuousToLp_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereContinuousToLp_injective

/-- info: 'GaussianTesting.SO3.zonalFourPolynomial_isHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.zonalFourPolynomial_isHomogeneous

/-- info: 'GaussianTesting.SO3.zonalFourPolynomial_laplacian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.zonalFourPolynomial_laplacian

/-- info: 'GaussianTesting.SO3.sphereZonalFour_eq_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereZonalFour_eq_polynomial

/-- info: 'GaussianTesting.SO3.sphereAxisContinuousAverage_zonalFour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereAxisContinuousAverage_zonalFour

/-- info: 'GaussianTesting.SO3.sphereKacTransition_spinFour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKacTransition_spinFour

/-- info: 'GaussianTesting.SO3.sphereSpinFour_toLp_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereSpinFour_toLp_ne_zero

/-- info: 'GaussianTesting.SO3.sphereMeanZeroKac_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereMeanZeroKac_norm_eq

/-- info: 'GaussianTesting.SO3.sphereMeanZeroKac_spectrum_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereMeanZeroKac_spectrum_subset

/-- info: 'GaussianTesting.SO3.sphereMeanZeroKac_sharp_mem_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereMeanZeroKac_sharp_mem_spectrum

/-- info: 'GaussianTesting.SO3.sphereMeanZeroKac_isGreatest_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereMeanZeroKac_isGreatest_spectrum

/-- info: 'GaussianTesting.SO3.sphereKac_spectralGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.SO3.sphereKac_spectralGap

-- The contracted acceptance operator and projective critical points after Lemma 3.1.

/-- info: 'GaussianTesting.TensorSquare.contractionOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.contractionOperator_apply

/-- info: 'GaussianTesting.TensorSquare.contractionOperator_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.contractionOperator_isPositive

/-- info: 'GaussianTesting.TensorSquare.norm_contractionOperator_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.norm_contractionOperator_le_one

/-- info: 'GaussianTesting.TensorSquare.contractionOperator_first_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.contractionOperator_first_moment

/-- info: 'GaussianTesting.TensorSquare.contractionOperator_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.contractionOperator_second_moment

/-- info: 'GaussianTesting.TensorSquare.norm_gradAccA_sq_eq_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.norm_gradAccA_sq_eq_variance

/-- info: 'GaussianTesting.TensorSquare.gradAccA_eq_zero_iff_contractionOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.gradAccA_eq_zero_iff_contractionOperator

/-- info: 'GaussianTesting.contraction_criticalPoint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.contraction_criticalPoint_iff

-- Pure-state trace norm and the two versions of Theorem 1.1.

/-- info: 'GaussianTesting.pureStateDifference_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureStateDifference_cube

/-- info: 'GaussianTesting.abs_pureStateDifference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.abs_pureStateDifference

/-- info: 'GaussianTesting.isPositiveTraceClass_abs_pureStateDifference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.isPositiveTraceClass_abs_pureStateDifference

/-- info: 'GaussianTesting.traceNorm_pureStateDifference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.traceNorm_pureStateDifference

/-- info: 'GaussianTesting.pureStateTraceDistance_eq_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureStateTraceDistance_eq_sqrt

/-- info: 'GaussianTesting.pureStateTraceDistance_eq_half_traceNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureStateTraceDistance_eq_half_traceNorm

/-- info: 'GaussianTesting.le_pureStateTraceDistance_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.le_pureStateTraceDistance_iff

/-- info: 'GaussianTesting.pureFidelity_sq_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureFidelity_sq_le_iff

/-- info: 'GaussianTesting.fermionic_gaussian_testing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionic_gaussian_testing

/-- info: 'GaussianTesting.bosonic_gaussian_testing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.bosonic_gaussian_testing

/-- info: 'GaussianTesting.fermionic_gaussian_testing_traceDistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionic_gaussian_testing_traceDistance

/-- info: 'GaussianTesting.bosonic_gaussian_testing_traceDistance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.bosonic_gaussian_testing_traceDistance

-- Figure 1(a): explicit Bell basis, classical eigenvalue rule, and accepting projection.

/-- info: 'GaussianTesting.fermionicBellVector_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicBellVector_orthonormal

/-- info: 'GaussianTesting.majoranaPair_fermionicBellVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.majoranaPair_fermionicBellVector

/-- info: 'GaussianTesting.lambdaF_fermionicBellBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.lambdaF_fermionicBellBasis

/-- info: 'GaussianTesting.fermionicBellMeasurement_eq_PF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicBellMeasurement_eq_PF

/-- info: 'GaussianTesting.fermionicBellReadout_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicBellReadout_probability

/-- info: 'GaussianTesting.fermionicBellMeasurement_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicBellMeasurement_acceptance

-- Corollary 5.3: repeated measurements on fresh pairs and the copy bound.

/-- info: 'GaussianTesting.fermionic_acceptance_le_of_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionic_acceptance_le_of_far

/-- info: 'GaussianTesting.fermionicTestProtocol_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicTestProtocol_acceptance

/-- info: 'GaussianTesting.fermionicTestProtocol_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicTestProtocol_rejection

/-- info: 'GaussianTesting.fermionic_testing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionic_testing

/-- info: 'GaussianTesting.fermionicTestCopies_le_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicTestCopies_le_rate

-- Theorem 5.2 and the required second-quantized copy action.

/-- info: 'GaussianTesting.fermionSecondQuantization_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionSecondQuantization_implements

/-- info: 'GaussianTesting.continuous_fermionSecondQuantization_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.continuous_fermionSecondQuantization_orbit

/-- info: 'GaussianTesting.fermionExteriorEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionExteriorEquiv

/-- info: 'GaussianTesting.fermionSecondQuantization_exteriorPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionSecondQuantization_exteriorPower

/-- info: 'GaussianTesting.fermionTripleEquiv_majorana' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionTripleEquiv_majorana

/-- info: 'GaussianTesting.fermionCopyRepresentation_majorana' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionCopyRepresentation_majorana

/-- info: 'GaussianTesting.fermion_copyRepresentation_axis_derivatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermion_copyRepresentation_axis_derivatives

/-- info: 'GaussianTesting.fermion_Sop_eq_kacAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermion_Sop_eq_kacAverage

/-- info: 'GaussianTesting.fermionic_spectrum_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionic_spectrum_subset

/-- info: 'GaussianTesting.finite_robustness_of_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.finite_robustness_of_spectrum

/-- info: 'GaussianTesting.fermionic_fidelity_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionic_fidelity_witness

/-- info: 'GaussianTesting.fermionic_fidelity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionic_fidelity

-- Lemma 5.1: manuscript normal form, covariance transport, and occupation saturation.

/-- info: 'GaussianTesting.exists_specialOrthogonal_skewNormalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.exists_specialOrthogonal_skewNormalForm

/-- info: 'GaussianTesting.lambdaF_eq_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.lambdaF_eq_ladder

/-- info: 'GaussianTesting.ImplementsMajoranaRotation.lambdaF_conjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ImplementsMajoranaRotation.lambdaF_conjugate

/-- info: 'GaussianTesting.ImplementsMajoranaRotation.accProb_PF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ImplementsMajoranaRotation.accProb_PF

/-- info: 'GaussianTesting.ImplementsMajoranaRotation.covMat_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ImplementsMajoranaRotation.covMat_symm

/-- info: 'GaussianTesting.ImplementsMajoranaRotation.sum_sq_covMat_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ImplementsMajoranaRotation.sum_sq_covMat_symm

/-- info: 'GaussianTesting.exists_phase_basis_of_covMat_skewBlockMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.exists_phase_basis_of_covMat_skewBlockMatrix

/-- info: 'GaussianTesting.fermionicGaussian_iff_lambdaF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicGaussian_iff_lambdaF

/-- info: 'GaussianTesting.fermionicGaussian_iff_accProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicGaussian_iff_accProb

-- Section 5 background: independent SO(2m) implementers and parity orbits.

/-- info: 'GaussianTesting.exists_gaussianImplementer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.exists_gaussianImplementer

/-- info: 'GaussianTesting.gaussianUnitaryGroup_eq_planeUnitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.gaussianUnitaryGroup_eq_planeUnitaryGroup

/-- info: 'GaussianTesting.gaussianImplementer_majorana' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.gaussianImplementer_majorana

/-- info: 'GaussianTesting.gaussianUnitary_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.gaussianUnitary_parity

/-- info: 'GaussianTesting.mem_fermionicGaussianOrbit_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.mem_fermionicGaussianOrbit_iff

/-- info: 'GaussianTesting.fermionicGaussianStates_eq_isGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicGaussianStates_eq_isGaussian

/-- info: 'GaussianTesting.oddFermionicGaussianStates_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.oddFermionicGaussianStates_zero

/-- info: 'GaussianTesting.bosonic_physical_testing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.bosonic_physical_testing

/-- info: 'GaussianTesting.testingCopies_le_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.testingCopies_le_rate

/-- info: 'GaussianTesting.fourCopyNumberMeasurement_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fourCopyNumberMeasurement_acceptance

/-- info: 'GaussianTesting.meanZeroNumberMeasurement_eq_P0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.meanZeroNumberMeasurement_eq_P0

/-- info: 'GaussianTesting.schrodinger_gaussian_fidelity_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_gaussian_fidelity_witness

/-- info: 'GaussianTesting.schrodinger_meanZero_fidelity_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_meanZero_fidelity_witness

/-- info: 'GaussianTesting.schrodinger_meanZero_spectrum_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_meanZero_spectrum_subset

/-- info: 'GaussianTesting.coherentNumberMeasurement_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.coherentNumberMeasurement_acceptance

/-!
# Axioms of the main theorems

Run `lake env lean scripts/Audit.lean` after `lake build`.

Each guarded command requires exactly the standard foundational axioms below.
A new axiom dependency, a missing declaration, or an unexpected diagnostic makes
the audit fail.
-/

-- Abstract and finite-dimensional robustness theorems.

/-- info: 'GaussianTesting.TensorSquare.robust_testing_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.TensorSquare.robust_testing_abstract

/-- info: 'GaussianTesting.robust_testing_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.robust_testing_of_gap

-- Spectral gap and fermionic endpoints.

/-- info: 'GaussianTesting.kacT_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.kacT_gap

/-- info: 'GaussianTesting.UnitaryRepresentation.irreducibleSpan_dense_haar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.UnitaryRepresentation.irreducibleSpan_dense_haar

/-- info: 'GaussianTesting.SO3.exists_angularMomentum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.SO3.exists_angularMomentum

/-- info: 'GaussianTesting.SO3.kacAverage_spectrum_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.SO3.kacAverage_spectrum_subset

-- Bosonic spectral and exact-characterization endpoints.

/-- info: 'GaussianTesting.blockGapQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.blockGapQ

/-- info: 'GaussianTesting.three_projection_gap_of_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.three_projection_gap_of_gram

-- Bosonic robustness and repetition endpoints.

/-- info: 'GaussianTesting.main_boson_mean_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.main_boson_mean_zero

/-- info: 'GaussianTesting.main_boson_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.main_boson_coherent

/-- info: 'GaussianTesting.IsPositiveTraceClass.hasSum_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.IsPositiveTraceClass.hasSum_diagonal

/-- info: 'GaussianTesting.isPositiveTraceClass_iff_summable_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.isPositiveTraceClass_iff_summable_diagonal

/-- info: 'GaussianTesting.isDensityOperator_iff_hasSum_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.isDensityOperator_iff_hasSum_diagonal

/--
info: 'GaussianTesting.IsDensityOperator.exists_normalized_gram_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms GaussianTesting.IsDensityOperator.exists_normalized_gram_representation

/--
info: 'GaussianTesting.isDensityOperator_iff_exists_gram_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms GaussianTesting.isDensityOperator_iff_exists_gram_representation

/-- info: 'GaussianTesting.boson_mean_zero_testing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.boson_mean_zero_testing

/-- info: 'GaussianTesting.boson_coherent_testing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.boson_coherent_testing

/-- info: 'GaussianTesting.coherent_polynomial_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.coherent_polynomial_gap

-- Eq. (3.2) and the linear fidelity bounds in Sections 3, 5 and 6.

/-- info: 'GaussianTesting.overlap_le_pureFidelity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.overlap_le_pureFidelity

/-- info: 'GaussianTesting.pureFidelity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.pureFidelity_nonneg

/-- info: 'GaussianTesting.pureFidelity_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.pureFidelity_le_one

/-- info: 'GaussianTesting.sq_overlap_le_pureFidelity_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.sq_overlap_le_pureFidelity_sq

/-- info: 'GaussianTesting.pureFidelity_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GaussianTesting.pureFidelity_phase

-- Theorem 3.4 and its consequence in Theorem 1.2.

/-- info: 'GaussianTesting.projective_angle_le_of_chord_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.projective_angle_le_of_chord_bound

/-- info: 'GaussianTesting.angular_witness_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.angular_witness_of_gap

/-- info: 'GaussianTesting.TensorSquare.angular_witness_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.angular_witness_abstract

/-- info: 'GaussianTesting.robust_testing_of_gap_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.robust_testing_of_gap_sharp

/-- info: 'GaussianTesting.TensorSquare.robust_testing_abstract_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.robust_testing_abstract_sharp

/-- info: 'GaussianTesting.RobustnessBounds.angular_fidelity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.RobustnessBounds.angular_fidelity

/-- info: 'GaussianTesting.RobustnessBounds.linear_fidelity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.RobustnessBounds.linear_fidelity

/-- info: 'GaussianTesting.testing_fidelity_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.testing_fidelity_of_gap

/-- info: 'GaussianTesting.TensorSquare.testing_fidelity_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.testing_fidelity_abstract

-- Spectral equivalence in Lemma 3.3 and the coherent-test spectrum in Lemma 6.6.

/-- info: 'GaussianTesting.spectrum_gap_iff_polynomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.spectrum_gap_iff_polynomial_nonneg

/-- info: 'GaussianTesting.coherent_spectrum_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.coherent_spectrum_subset

-- The completed tensor cube, its moments, and the spectral gradient and fidelity bounds.

/-- info: 'GaussianTesting.threeCopyAverage_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeCopyAverage_eq

/-- info: 'GaussianTesting.threeCopyAverage_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeCopyAverage_moments

/-- info: 'GaussianTesting.lojasiewiczData_of_threeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.lojasiewiczData_of_threeCopy_spectrum

/-- info: 'GaussianTesting.norm_gradAcc_sq_ge_of_threeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.norm_gradAcc_sq_ge_of_threeCopy_spectrum

-- The symmetric-cube strengthening in the footnote before Lemma 3.3.

/-- info: 'GaussianTesting.threeCopyAverage_maps_symmetricCube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeCopyAverage_maps_symmetricCube

/-- info: 'GaussianTesting.symmetricThreeCopyAverage_positive_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.symmetricThreeCopyAverage_positive_contraction

/-- info: 'GaussianTesting.symmetricThreeCopyAverage_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.symmetricThreeCopyAverage_moments

/-- info: 'GaussianTesting.lojasiewiczData_of_symmetricThreeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.lojasiewiczData_of_symmetricThreeCopy_spectrum

/-- info: 'GaussianTesting.norm_gradAcc_sq_ge_of_symmetricThreeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.norm_gradAcc_sq_ge_of_symmetricThreeCopy_spectrum

/-- info: 'GaussianTesting.robustness_of_threeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.robustness_of_threeCopy_spectrum

/-- info: 'GaussianTesting.angular_witness_of_threeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.angular_witness_of_threeCopy_spectrum

/-- info: 'GaussianTesting.angular_fidelity_of_threeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.angular_fidelity_of_threeCopy_spectrum

/-- info: 'GaussianTesting.testing_fidelity_of_threeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.testing_fidelity_of_threeCopy_spectrum

-- Local unit-vector solutions and the energy identity in Lemma 3.1.

/-- info: 'GaussianTesting.TensorSquare.contDiff_gradAccA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.contDiff_gradAccA

/-- info: 'GaussianTesting.TensorSquare.IsUnitFlowOn.contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsUnitFlowOn.contDiffOn

/-- info: 'GaussianTesting.TensorSquare.exists_smooth_local_unitFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.exists_smooth_local_unitFlow

/-- info: 'GaussianTesting.TensorSquare.IsUnitFlowOn.eqOn_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsUnitFlowOn.eqOn_overlap

/-- info: 'GaussianTesting.TensorSquare.IsUnitFlowOn.hasDerivWithinAt_accProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsUnitFlowOn.hasDerivWithinAt_accProb

/-- info: 'GaussianTesting.TensorSquare.IsUnitFlowOn.integral_norm_grad_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsUnitFlowOn.integral_norm_grad_sq_eq

/-- info: 'GaussianTesting.TensorSquare.IsUnitFlowOn.integral_norm_velocity_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsUnitFlowOn.integral_norm_velocity_sq_eq

-- Ray charts, the Fubini–Study metric, and global continuation in Lemma 3.1.

/-- info: 'GaussianTesting.TensorSquare.gradAccA_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.gradAccA_phase

/-- info: 'GaussianTesting.TensorSquare.inner_gradAccA_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.inner_gradAccA_eq_zero

/-- info: 'GaussianTesting.contDiffOn_rayTransition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.contDiffOn_rayTransition

/-- info: 'GaussianTesting.rayDist_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.rayDist_mk

/-- info: 'GaussianTesting.rayCompleteSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.rayCompleteSpace

/-- info: 'GaussianTesting.TensorSquare.IsUnitFlowOn.projective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsUnitFlowOn.projective

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.eqOn_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.eqOn_Icc

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.exists_unit_lift_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.exists_unit_lift_Icc

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.dist_sq_le_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.dist_sq_le_energy

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.exists_limit_Ico' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.exists_limit_Ico

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.continue_at_finite_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.continue_at_finite_time

/-- info: 'GaussianTesting.exists_global_of_finite_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.exists_global_of_finite_extension

/-- info: 'GaussianTesting.TensorSquare.exists_unique_smooth_projectiveFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.exists_unique_smooth_projectiveFlow

/-- info: 'GaussianTesting.projective_gradient_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.projective_gradient_flow

-- Certainty states and the largest eigenvalue after Lemma 3.2.

/-- info: 'GaussianTesting.threeCopyAverage_fixed_iff_accProb_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeCopyAverage_fixed_iff_accProb_eq_one

/-- info: 'GaussianTesting.threeCopyAverage_hasEigenvalue_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeCopyAverage_hasEigenvalue_one

/-- info: 'GaussianTesting.threeCopyAverage_spectrum_subset_unitInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeCopyAverage_spectrum_subset_unitInterval

/-- info: 'GaussianTesting.threeCopyAverage_isGreatest_eigenvalue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeCopyAverage_isGreatest_eigenvalue

-- The derivative bounds and Fubini–Study speed in Eq. (3.7).

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.hasDerivWithinAt_rayAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.hasDerivWithinAt_rayAcceptance

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.rayAcceptance_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.rayAcceptance_mono

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.tendsto_dist_div_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.tendsto_dist_div_time

/-- info: 'GaussianTesting.rayGradientNormSq_ge_of_threeCopy_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.rayGradientNormSq_ge_of_threeCopy_spectrum

/-- info: 'GaussianTesting.ray_flow_derivative_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_flow_derivative_bounds

-- The tangent metric and the gradient of ray acceptance in Eq. (3.4).

/-- info: 'GaussianTesting.tendsto_rayTangentMetric_of_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.tendsto_rayTangentMetric_of_dist

/-- info: 'GaussianTesting.TensorSquare.hasFDerivAt_accProbA_rayChartSection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.hasFDerivAt_accProbA_rayChartSection

/-- info: 'GaussianTesting.TensorSquare.isFubiniStudyGradient_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.isFubiniStudyGradient_iff

/-- info: 'GaussianTesting.fubiniStudyGradient_rayAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fubiniStudyGradient_rayAcceptance

-- Strict increase and convergence after Eq. (3.7) in Theorem 3.4.

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.one_sub_rayAcceptance_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.one_sub_rayAcceptance_ge

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.rayAcceptance_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.rayAcceptance_lt_one

/-- info: 'GaussianTesting.rayAcceptance_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.rayAcceptance_tendsto_one

/-- info: 'GaussianTesting.rayAcceptance_strictMonoOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.rayAcceptance_strictMonoOn

/-- info: 'GaussianTesting.ray_acceptance_strictly_increases_to_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_acceptance_strictly_increases_to_one

-- Path length, the Cauchy property, and the certainty limit in Theorem 3.4.

/-- info: 'GaussianTesting.TensorSquare.IsProjectiveFlowOn.dist_le_integral_speed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.IsProjectiveFlowOn.dist_le_integral_speed

/-- info: 'GaussianTesting.ray_integral_speed_le_potential_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_integral_speed_le_potential_sub

/-- info: 'GaussianTesting.ray_dist_le_potential_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_dist_le_potential_sub

/-- info: 'GaussianTesting.ray_dist_le_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_dist_le_potential

/-- info: 'GaussianTesting.TensorSquare.continuous_rayAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.TensorSquare.continuous_rayAcceptance

/-- info: 'GaussianTesting.ray_trajectory_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_trajectory_cauchy

/-- info: 'GaussianTesting.ray_trajectory_tendsto_certainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_trajectory_tendsto_certainty

/-- info: 'GaussianTesting.ray_trajectory_tendsto_certaintyState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.ray_trajectory_tendsto_certaintyState

-- Lemma 6.2: arbitrary density operators, actual wavefunctions, and the graph-closed test.

/-- info: 'GaussianTesting.operatorTrace_mul_gramOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.operatorTrace_mul_gramOp

/-- info: 'GaussianTesting.IsPositiveTraceClass.mul_hasSum_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.IsPositiveTraceClass.mul_hasSum_diagonal

/-- info: 'GaussianTesting.densityTensor_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.densityTensor_tp

/-- info: 'GaussianTesting.P0B_eq_closedLambdaB_kernelProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.P0B_eq_closedLambdaB_kernelProjection

/-- info: 'GaussianTesting.HilbertDensity.IsDensityOperator.exists_normalized_gram_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.IsDensityOperator.exists_normalized_gram_representation

/-- info: 'GaussianTesting.HilbertDensity.signedSwap_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.signedSwap_trace

/-- info: 'GaussianTesting.HilbertDensity.signedSwap_trace_norm_le_purity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.signedSwap_trace_norm_le_purity

/-- info: 'GaussianTesting.HilbertDensity.IsDensityOperator.purity_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.IsDensityOperator.purity_le_norm

/-- info: 'GaussianTesting.polynomialGaussianFun_creation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.polynomialGaussianFun_creation

/-- info: 'GaussianTesting.polynomialGaussianFun_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.polynomialGaussianFun_annihilation

/-- info: 'GaussianTesting.schrodingerFiniteFockGraph_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerFiniteFockGraph_hasDerivAt

/-- info: 'GaussianTesting.schrodingerLambda_eq_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerLambda_eq_closure

/-- info: 'GaussianTesting.schrodingerLambda_hasCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerLambda_hasCore

/-- info: 'GaussianTesting.schrodingerRotation_P0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerRotation_P0

/-- info: 'GaussianTesting.schrodingerRotation_quarter_waveTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerRotation_quarter_waveTensor

/-- info: 'GaussianTesting.schrodingerDensityTensor_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerDensityTensor_product

/-- info: 'GaussianTesting.schrodinger_signedSwap_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_signedSwap_trace

/-- info: 'GaussianTesting.purity_schrodinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.purity_schrodinger

/-- info: 'GaussianTesting.schrodinger_acceptance_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_acceptance_real

/-- info: 'GaussianTesting.schrodinger_acceptance_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_acceptance_mem_Icc

-- The four-copy projection and its actual partial-trace expectation.

/-- info: 'GaussianTesting.waveTensor_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveTensor_surjective

/-- info: 'GaussianTesting.HilbertDensity.operatorTrace_mul_reducedRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.operatorTrace_mul_reducedRight

/-- info: 'GaussianTesting.HilbertDensity.reducedRight_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.reducedRight_basis

/-- info: 'GaussianTesting.HilbertDensity.reducedRight_reshuffle_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.reducedRight_reshuffle_square

/-- info: 'GaussianTesting.fourCopyProjection_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fourCopyProjection_symmetric

/-- info: 'GaussianTesting.fourCopyProjection_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fourCopyProjection_idempotent

/-- info: 'GaussianTesting.schrodingerFourCopyProjection_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerFourCopyProjection_idempotent

/-- info: 'GaussianTesting.schrodingerFourCopyProjection_expectation_eq_reducedTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerFourCopyProjection_expectation_eq_reducedTrace

/-- info: 'GaussianTesting.schrodingerReducedState_isDensityOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerReducedState_isDensityOperator

/-- info: 'GaussianTesting.schrodingerReducedState_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerReducedState_basis

/-- info: 'GaussianTesting.schrodingerFourCopyAcceptance_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerFourCopyAcceptance_mem_Icc

-- The physical coherent-test projection and normalized vacuum.

/-- info: 'GaussianTesting.waveVacuum_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveVacuum_norm

/-- info: 'GaussianTesting.waveVacuum_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveVacuum_annihilation

/-- info: 'GaussianTesting.waveParity_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveParity_vacuum

/-- info: 'GaussianTesting.schrodingerTensorRotation_balanced_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerTensorRotation_balanced_swap

/-- info: 'GaussianTesting.schrodingerQ_isAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerQ_isAcceptance

/-- info: 'GaussianTesting.schrodingerQ_swap_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerQ_swap_left

/-- info: 'GaussianTesting.schrodingerQ_expectation_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerQ_expectation_real

/-- info: 'GaussianTesting.schrodingerCoherentAcceptance_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerCoherentAcceptance_mem_Icc

/-- info: 'GaussianTesting.schrodingerQ_expectation_eq_reducedTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerQ_expectation_eq_reducedTrace

-- Explicit Weyl action and elementary characteristic-function properties.

/-- info: 'GaussianTesting.weylOperator_coeFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.weylOperator_coeFn

/-- info: 'GaussianTesting.weylOperator_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.weylOperator_mul

/-- info: 'GaussianTesting.weylOperator_symm_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.weylOperator_symm_neg

/-- info: 'GaussianTesting.weylOperator_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.weylOperator_adjoint

/-- info: 'GaussianTesting.weylOperator_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.weylOperator_norm

/-- info: 'GaussianTesting.continuous_weylOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.continuous_weylOperator

/-- info: 'GaussianTesting.continuous_weylOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.continuous_weylOperator_apply

/-- info: 'GaussianTesting.waveCharacteristic_gramOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveCharacteristic_gramOp

/-- info: 'GaussianTesting.waveCharacteristic_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveCharacteristic_basis

/-- info: 'GaussianTesting.waveCharacteristic_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveCharacteristic_zero

/-- info: 'GaussianTesting.norm_waveCharacteristic_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.norm_waveCharacteristic_le_one

/-- info: 'GaussianTesting.waveCharacteristic_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveCharacteristic_neg

/-- info: 'GaussianTesting.continuous_waveCharacteristic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.continuous_waveCharacteristic

-- Section 6: vacuum characteristic functions, covariance, and actions on copies.

/-- info: 'GaussianTesting.waveCharacteristic_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveCharacteristic_rankOne

/-- info: 'GaussianTesting.pureWaveCharacteristic_displacement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureWaveCharacteristic_displacement

/-- info: 'GaussianTesting.inner_waveVacuum_weylOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.inner_waveVacuum_weylOperator

/-- info: 'GaussianTesting.pureWaveCharacteristic_displaced_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureWaveCharacteristic_displaced_vacuum

/-- info: 'GaussianTesting.vacuumCharacteristic_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.vacuumCharacteristic_balanced

/-- info: 'GaussianTesting.schrodingerTensorRotation_balanced_weyl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerTensorRotation_balanced_weyl

/-- info: 'GaussianTesting.pureTensorCharacteristic_tmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureTensorCharacteristic_tmul

/-- info: 'GaussianTesting.pureTensorCharacteristic_balanced_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureTensorCharacteristic_balanced_product

/-- info: 'GaussianTesting.schrodingerCopiesAction_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerCopiesAction_mul

/-- info: 'GaussianTesting.continuous_schrodingerSpecialOrthogonalRepresentation_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.continuous_schrodingerSpecialOrthogonalRepresentation_apply

/-- info: 'GaussianTesting.schrodingerSpecialOrthogonalRepresentation_planeRotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerSpecialOrthogonalRepresentation_planeRotation

-- Physical background and the manuscript proofs of Propositions 6.1 and 6.3.

/-- info: 'GaussianTesting.rankOne_eq_of_pureWaveCharacteristic_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.rankOne_eq_of_pureWaveCharacteristic_eq

/-- info: 'GaussianTesting.denseRange_polynomialGaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.denseRange_polynomialGaussian

/-- info: 'GaussianTesting.inner_polynomialGaussian_creation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.inner_polynomialGaussian_creation

/-- info: 'GaussianTesting.inner_polynomialGaussian_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.inner_polynomialGaussian_annihilation

/-- info: 'GaussianTesting.polynomialAnnihilation_creation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.polynomialAnnihilation_creation

/-- info: 'GaussianTesting.finiteFockPolynomialCore_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.finiteFockPolynomialCore_eq_top

/-- info: 'GaussianTesting.schrodingerFiniteLambda_domain_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerFiniteLambda_domain_dense

/-- info: 'GaussianTesting.schrodingerLambda_domain_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerLambda_domain_dense

/-- info: 'GaussianTesting.characteristic_rotation_eq_exp_nonpos_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.characteristic_rotation_eq_exp_nonpos_quadratic

/-- info: 'GaussianTesting.pureWaveCharacteristic_balanced_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureWaveCharacteristic_balanced_of_kernel

/-- info: 'GaussianTesting.pureWaveCharacteristic_kernel_eq_exp_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureWaveCharacteristic_kernel_eq_exp_quadratic

/-- info: 'GaussianTesting.continuous_character_eq_weyl_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.continuous_character_eq_weyl_phase

/-- info: 'GaussianTesting.coherent_factorization_normalized_character' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.coherent_factorization_normalized_character

/-- info: 'GaussianTesting.coherent_factorization_eq_displaced_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.coherent_factorization_eq_displaced_vacuum

/-- info: 'GaussianTesting.schrodingerCoherentAcceptance_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerCoherentAcceptance_eq_one_iff

-- Required physical representation and Gaussian-invariance links.

/-- info: 'GaussianTesting.orthonormal_schrodingerNumberVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.orthonormal_schrodingerNumberVector

/-- info: 'GaussianTesting.dense_span_schrodingerNumberVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.dense_span_schrodingerNumberVector

/-- info: 'GaussianTesting.fockSchrodingerEquiv_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fockSchrodingerEquiv_vacuum

/-- info: 'GaussianTesting.polynomialCreation_schrodingerNumberPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.polynomialCreation_schrodingerNumberPolynomial

/-- info: 'GaussianTesting.polynomialAnnihilation_schrodingerNumberPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.polynomialAnnihilation_schrodingerNumberPolynomial

/-- info: 'GaussianTesting.fockPairGraphEquiv_closedGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fockPairGraphEquiv_closedGraph

/-- info: 'GaussianTesting.fockPairSchrodingerEquiv_P0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fockPairSchrodingerEquiv_P0B

/-- info: 'GaussianTesting.fockPairSchrodingerEquiv_tpPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fockPairSchrodingerEquiv_tpPair

/-- info: 'GaussianTesting.schrodingerLambda_mem_kernel_iff_rotation_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerLambda_mem_kernel_iff_rotation_fixed

/-- info: 'GaussianTesting.waveQuadraticPhase_weyl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveQuadraticPhase_weyl

/-- info: 'GaussianTesting.waveLinearChange_weyl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveLinearChange_weyl

/-- info: 'GaussianTesting.waveFourier_conjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveFourier_conjugate

/-- info: 'GaussianTesting.schrodingerFourier_waveTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerFourier_waveTensor

/-- info: 'GaussianTesting.symplectic_hasWaveImplementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.symplectic_hasWaveImplementation

/-- info: 'GaussianTesting.waveSymplecticUnitary_conjugate_weyl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveSymplecticUnitary_conjugate_weyl

/-- info: 'GaussianTesting.waveSymplecticUnitary_commutesWithCopyRotations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveSymplecticUnitary_commutesWithCopyRotations

/-- info: 'GaussianTesting.pureWaveCharacteristic_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.pureWaveCharacteristic_symplectic

/-- info: 'GaussianTesting.waveSymplecticUnitary_tensorP0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveSymplecticUnitary_tensorP0

/-- info: 'GaussianTesting.waveTensor_vacuum_mem_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveTensor_vacuum_mem_kernel

/-- info: 'GaussianTesting.schrodingerTensorP0_symplectic_vacuum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerTensorP0_symplectic_vacuum

-- Gaussian reconstruction, pure-state reduction, and the physical test operators.

/-- info: 'GaussianTesting.norm_pureWaveCharacteristic_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.norm_pureWaveCharacteristic_lt_one

/-- info: 'GaussianTesting.gaussianCharacteristic_neg_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.gaussianCharacteristic_neg_posDef

/-- info: 'GaussianTesting.exists_symplectic_vacuum_of_quadratic_wavefunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.exists_symplectic_vacuum_of_quadratic_wavefunction

/-- info: 'GaussianTesting.exists_symplectic_vacuum_of_pureCharacteristic_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.exists_symplectic_vacuum_of_pureCharacteristic_quadratic

/-- info: 'GaussianTesting.exists_displaced_symplectic_vacuum_of_gaussian_characteristic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.exists_displaced_symplectic_vacuum_of_gaussian_characteristic

/-- info: 'GaussianTesting.HilbertDensity.IsDensityOperator.exists_rankOne_of_norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.IsDensityOperator.exists_rankOne_of_norm_eq_one

/-- info: 'GaussianTesting.HilbertDensity.exists_unit_tmul_of_reducedRight_eq_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.exists_unit_tmul_of_reducedRight_eq_rankOne

/-- info: 'GaussianTesting.waveNumberCoordinates_conj_P0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveNumberCoordinates_conj_P0

/-- info: 'GaussianTesting.fockPairSchrodingerEquiv_ULp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fockPairSchrodingerEquiv_ULp

/-- info: 'GaussianTesting.fockPairSchrodingerEquiv_VLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fockPairSchrodingerEquiv_VLp

/-- info: 'GaussianTesting.waveNumberCoordinates_conj_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.waveNumberCoordinates_conj_Q

/-- info: 'GaussianTesting.schrodingerCoherentAverage_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerCoherentAverage_spectrum

/-- info: 'GaussianTesting.schrodinger_coherent_spectrum_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_coherent_spectrum_subset

-- Complete physical Proposition 6.1.

/-- info: 'GaussianTesting.bosonicMeanZeroGaussian_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.bosonicMeanZeroGaussian_characterization

/-- info: 'GaussianTesting.schrodingerMeanZeroAcceptance_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerMeanZeroAcceptance_eq_one_iff

-- Complete physical Proposition 6.3, including its manuscript purity reduction.

/-- info: 'GaussianTesting.schrodingerReducedState_rankOne_of_acceptance_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerReducedState_rankOne_of_acceptance_one

/-- info: 'GaussianTesting.gaussian_factorization_of_fourCopyAcceptance_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.gaussian_factorization_of_fourCopyAcceptance_one

/-- info: 'GaussianTesting.schrodingerFourCopyAcceptance_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerFourCopyAcceptance_eq_one_iff

/-- info: 'GaussianTesting.bosonicGaussian_and_coherent_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.bosonicGaussian_and_coherent_characterization

-- Physical Theorem 6.5, including its coherent comparison state.

/-- info: 'GaussianTesting.schrodinger_coherent_fidelity_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_coherent_fidelity_witness

/-- info: 'GaussianTesting.schrodinger_coherent_fidelity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodinger_coherent_fidelity

-- Gaussian-square span and perfect-completeness optimality.

/-- info: 'GaussianTesting.fermionicGaussianSquareSpan_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicGaussianSquareSpan_eq_kernel

/-- info: 'GaussianTesting.swap2_PF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.swap2_PF

/-- info: 'GaussianTesting.closedSpan_projection_le_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.closedSpan_projection_le_effect

/-- info: 'GaussianTesting.fermionicTest_projection_le_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicTest_projection_le_effect

/-- info: 'GaussianTesting.fermionicTest_acceptance_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionicTest_acceptance_le

-- Exact manuscript Gram calculations for Theorem 4.1 and Lemma 6.6.

/-- info: 'GaussianTesting.alternating_choose_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.alternating_choose_sq_sum

/-- info: 'GaussianTesting.spinKacMaximum_lt_of_six_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.spinKacMaximum_lt_of_six_le

/-- info: 'GaussianTesting.AngularMomentum.kacT_mem_spectrum_iff_of_integer_spin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.AngularMomentum.kacT_mem_spectrum_iff_of_integer_spin

/-- info: 'GaussianTesting.AngularMomentum.kacT_isGreatest_eigenvalue_of_integer_spin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.AngularMomentum.kacT_isGreatest_eigenvalue_of_integer_spin

/-- info: 'GaussianTesting.AngularMomentum.kacGapOn_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.AngularMomentum.kacGapOn_all

/-- info: 'GaussianTesting.threeVectorGram_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.threeVectorGram_spectrum

/-- info: 'GaussianTesting.three_family_average_mem_spectrum_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.three_family_average_mem_spectrum_iff

/-- info: 'GaussianTesting.coherentSectorMaxEigenvalue_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.coherentSectorMaxEigenvalue_lt_half

/-- info: 'GaussianTesting.blockSpectrumQ_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.blockSpectrumQ_nonzero

/-- info: 'GaussianTesting.three_projection_gap_of_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.three_projection_gap_of_gram

/-- info: 'GaussianTesting.coherent_spectrum_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.coherent_spectrum_subset

-- Explicit parity, two-copy rotations, pure density states, and difference-output moments.

/-- info: 'GaussianTesting.parityOp_eq_majoranaProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.parityOp_eq_majoranaProduct

/-- info: 'GaussianTesting.fermionPairEquiv_majorana' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionPairEquiv_majorana

/-- info: 'GaussianTesting.fermionPairMajorana_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionPairMajorana_sq

/-- info: 'GaussianTesting.fermionPairMajorana_anticomm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionPairMajorana_anticomm

/-- info: 'GaussianTesting.fermionPairRepresentation_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionPairRepresentation_hasDerivAt

/-- info: 'GaussianTesting.fermionPairRepresentation_fixed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fermionPairRepresentation_fixed_iff

/-- info: 'GaussianTesting.PF_eq_pairRotation_fixedProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.PF_eq_pairRotation_fixedProjection

/-- info: 'GaussianTesting.HilbertDensity.positiveTrace_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.positiveTrace_rankOne

/-- info: 'GaussianTesting.HilbertDensity.isPositiveTraceClass_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.isPositiveTraceClass_rankOne

/-- info: 'GaussianTesting.HilbertDensity.isDensityOperator_rankOne_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.isDensityOperator_rankOne_iff

/-- info: 'GaussianTesting.HilbertDensity.rankOne_eq_iff_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.rankOne_eq_iff_phase

/-- info: 'GaussianTesting.HilbertDensity.IsDensityOperator.norm_eq_one_iff_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.IsDensityOperator.norm_eq_one_iff_rankOne

/-- info: 'GaussianTesting.HilbertDensity.IsDensityOperator.idempotent_iff_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.IsDensityOperator.idempotent_iff_rankOne

/-- info: 'GaussianTesting.HilbertDensity.isDensityOperator_rayProjector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.isDensityOperator_rayProjector

/-- info: 'GaussianTesting.HilbertDensity.rayProjector_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.rayProjector_mk

/-- info: 'GaussianTesting.HilbertDensity.rayProjector_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.rayProjector_injective

/-- info: 'GaussianTesting.HilbertDensity.IsDensityOperator.existsUnique_rayProjector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.HilbertDensity.IsDensityOperator.existsUnique_rayProjector

/-- info: 'GaussianTesting.schrodingerDifference_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerDifference_even

/-- info: 'GaussianTesting.schrodingerReducedState_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerReducedState_even

/-- info: 'GaussianTesting.schrodingerDifferenceDensity_positionEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerDifferenceDensity_positionEvent

/-- info: 'GaussianTesting.schrodingerDifferenceFourierDensity_positionEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerDifferenceFourierDensity_positionEvent

/-- info: 'GaussianTesting.schrodingerDifferenceDensity_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerDifferenceDensity_normalized

/-- info: 'GaussianTesting.schrodingerReducedState_globalFirstMoments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerReducedState_globalFirstMoments

/-- info: 'GaussianTesting.schrodingerReducedState_firstMoments_of_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerReducedState_firstMoments_of_global

-- Bosonic Gaussian-square span and actual-test optimality.

/-- info: 'GaussianTesting.symmetricMixedLowering_jointKernel_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.symmetricMixedLowering_jointKernel_eq_zero

/-- info: 'GaussianTesting.mem_symmetricMixedAlgebra_of_balanced_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.mem_symmetricMixedAlgebra_of_balanced_swap

/-- info: 'GaussianTesting.polynomial_mem_copyGramAlgebra_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.polynomial_mem_copyGramAlgebra_of_invariant

/-- info: 'GaussianTesting.polynomialGaussian_mem_meanZeroGaussianSquareSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.polynomialGaussian_mem_meanZeroGaussianSquareSpan

/-- info: 'GaussianTesting.meanZeroGaussianSquareSpan_eq_symmetric_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.meanZeroGaussianSquareSpan_eq_symmetric_kernel

/-- info: 'GaussianTesting.mem_meanZeroGaussianSquareSpan_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.mem_meanZeroGaussianSquareSpan_iff

/-- info: 'GaussianTesting.meanZeroGaussianSquareSpan_projection_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.meanZeroGaussianSquareSpan_projection_square

/-- info: 'GaussianTesting.bosonicMeanZeroGaussian_optimality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.bosonicMeanZeroGaussian_optimality

-- Revised manuscript circuit and Gaussian covariance interfaces.

/-- info: 'GaussianTesting.fourCopyFigurePreparation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fourCopyFigurePreparation_eq

/-- info: 'GaussianTesting.fourCopyFigureProjection_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fourCopyFigureProjection_eq

/-- info: 'GaussianTesting.fourCopyNumberMeasurement_eq_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.fourCopyNumberMeasurement_eq_projection

/-- info: 'GaussianTesting.CommutesWithCopyRotations.meanZeroAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.CommutesWithCopyRotations.meanZeroAcceptance

/-- info: 'GaussianTesting.schrodingerMeanZeroAcceptance_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerMeanZeroAcceptance_symplectic

/-- info: 'GaussianTesting.schrodingerReducedState_covariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GaussianTesting.schrodingerReducedState_covariance
