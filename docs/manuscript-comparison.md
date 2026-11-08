# Comparison of the manuscript and the Lean formalization

This report explains how the Lean statements and proof strategies correspond
to [the manuscript](../material/manuscript.tex). The
[coverage guide](coverage.md) summarizes completed results and unused background;
the [manuscript index](manuscript-index.md) supplies individual source and
declaration links. The [development guide](development.md) describes the
reproducible checks.

## Final review, 2026-11-08

The review compared `material/manuscript.tex` with the public Lean statements
and the proof chains they actually invoke, including the required background
and four circuit readouts. It found no missing hypothesis or conclusion in
the 18 numbered results, and no new, unagreed proof-strategy deviation.
The mathematical scope is **the numbered results, their required supporting
claims, and Figure 1**, rather than every background assertion in the prose.

The updated manuscript was compared with the previous source and both versions
were compiled to verify references. All 18 numbered statements retain their
content and numbers; the changes to Sections 3–5 do not renumber equations.
Figure 1(d) now directly matches the Section 6 operator, using negative-angle
splitters on both pairs and retained outputs (2,4). Lemma 6.6 changes the names
of the center and complementary directions; Lean now uses `vVec` and `wVec`
accordingly. Section 6's new Eqs. (6.5), (6.6), (6.8), and (6.9) reference
existing acceptance and robustness arguments, with the last two recorded in
the Theorem 6.7 node. The expanded proof of Theorem 6.7 and the unchanged
statement of Lemma 6.2 require no different proof strategy.

| Results reviewed | Statement and proof alignment |
|---|---|
| Theorems 1.1 and 1.2 | The pointwise overlap promise and trace-distance formulation use the actual independent repeated-test protocols. The general fidelity corollary uses the manuscript's nonempty certainty set and applies Theorem 3.4 for every nonnegative error parameter. |
| Lemmas 3.1–3.3 and Theorem 3.4 | Arbitrary complete complex Hilbert spaces; actual completed tensor products; smooth unique projective continuation; both moment identities; spectral polynomial positivity; and the projective path-length/limit proof. The symmetric-cube strengthening before Lemma 3.3 is proved for the actual restricted operator. The same certainty witness supplies both robustness bounds. |
| Theorem 4.1 | The live proof uses the exact nonzero Gram eigenvalues, extends the bound by compact-group decomposition, identifies the spherical fixed space with constants, and proves sharpness with a degree-four harmonic. No finite-dimensionality or separability premise is imposed on the general representation. |
| Lemma 5.1, Theorem 5.2, Corollary 5.3 | Gaussianity is independently defined by the even and odd implementer orbits. Exactness uses covariance normal form and occupation saturation; robustness uses the actual second-quantized copy action, the Kac bound, and Theorem 3.4; repetition uses independent fresh pairs. No input parity assumption is added. |
| Propositions 6.1 and 6.3, Lemma 6.2 | Actual wavefunctions and the graph-closed generator kernel; characteristic positivity/polarization for centered exactness; arbitrary positive trace-one operators and the signed-swap purity argument; reduced-state purity, tensor factorization, inverse symplectic transport, and coherent reduction for general exactness. No finite-moment assumption is imposed on arbitrary tested inputs. |
| Theorems 6.4, 6.5 and 6.7, Lemma 6.6, Corollary 6.8 | The physical SO(3) action supplies the centered spectral bound; the coherent proof uses the exact occupation-block Gram spectrum and its physical conjugation. Theorem 3.4 gives constants 8 and 4. The top-eigenstate and coherent reduction gives constant 48. Repetition supplies explicit integer copy counts. |
| Figure 1(a–d) | All four panels give equality of the accepting operators on the full input spaces. In panel (d), both negative-angle splitters and the physical readout on outputs (2,4) give exactly the Section 6 four-copy operator. |

The introductory span and optimality assertions are also checked. The
fermionic span uses both parity classes, following the previously agreed
repair reflected in the manuscript's full-orthogonal-group twirling wording. The bosonic closed span is
the symmetric part of the kernel; its projection agrees with the actual
kernel test on identical inputs. The resulting comparisons allow every
positive contraction with perfect completeness. Difference-output evenness,
vanishing first moments when those moments exist, and the pure-state/density
and fermionic occupation interfaces are included in the review.

Implementation details preserve these arguments: arbitrary Hilbert bases
provide unitary coordinate identifications; finite occupation blocks are
assembled into the physical infinite-dimensional operators; and the
path-length integral is evaluated using its half-arcsine antiderivative.
None supplies an unproved mathematical premise. The section-by-section
discussion below and the [manuscript index](manuscript-index.md) identify the
corresponding declarations.

The exact copy count is `k⌈(C/ε²) log(1/δ)⌉`. The uniform bound retains
the additive `k`; the purely multiplicative bound is checked for
`δ ≤ exp(−1)`. This makes the manuscript's asymptotic rate precise,
including its existing comment about rounding near `δ=1`.

The manuscript takes the number of modes to satisfy `m ≥ 1`, as confirmed
by the author. Lean's coverage of zero modes is additional generality.
In particular, the `k=1,2` sharpness statement in the proof of Lemma 6.6
needs no qualification under the manuscript's convention.

The remaining qualifications in the index concern unused background or presentation: determination by
moments, the full covariance criteria, the many-copy commutant, the full complex
fermionic second-quantized action, mixed-state characteristic injectivity,
unused Gaussian ground-state/mean-operator descriptions, full unbounded
generator conjugation, and the abstract symmetric-Fock direct-sum packaging.
The specific prerequisites used by the numbered results are proved; none of
these entries is an assumed missing lemma in those proofs.

The [CI workflow](../.github/workflows/lean_action_ci.yml) now runs the existing
axiom audit, public-statement/proof-dependency checks, and manuscript declaration
checks after building Lean. It builds both blueprint editions and validates
the rendered links, declaration names, proof status, and both graph layouts.
Verification after the manuscript update passed a full `lake build` (4210 jobs),
both Lean audits, all 740 manuscript-linked declarations, and all 530 distinct
blueprint declarations. HTML and PDF generation passed, as did both dependency
layouts and their 130 bidirectional manuscript links. The regenerated index
has 79 entries: 71 checked, 6 partial, and 2 open; the two new checked entries
are intermediate equations within Theorem 6.7. All 22 equation labels agree
with the compiled manuscript. The reference parser has 17 regression tests,
also run in CI. A subsequent linter cleanup removed all 529 warning lines
without changing mathematical statements or proof strategies or disabling
linters. The full 4210-job build and both Lean audits pass. CI also runs a
whole-library check for `sorry`, including private helpers and import coverage.
Site assembly also passed, checking all 530 blueprint declaration links and
190 local homepage links. Blueprint Lean links now point directly to the
declaration's source on GitHub at the built commit; CI checks these source
locations without generating separate API documentation. The static dependency
graph was regenerated and visually checked using installed Graphviz; its renderer
no longer downloads a JavaScript package on each run.
This review and the automated checks do not replace an independent author
review of the mathematical statements. Future manuscript or proof changes
must be compared again, rather than relying on this dated review.

## Gradient flow and fidelity

Lean implements the manuscript's fidelity `pureFidelity G ψ` as the supremum
of the absolute overlaps. For a nonempty class of unit vectors and a unit input,
the fidelity lies in `[0,1]`, and each witness overlap bounds it from below.
Changing the phase of the input preserves the fidelity.
`pureFidelity_sq_le_iff` proves that a bound on squared class fidelity is
equivalent to the same bound on the squared overlap with every member of a
nonempty unit-vector class. This is the link between Theorem 1.1's pointwise
promise and the testing corollaries.
[Eq. (3.2) in Lean](../GaussianTesting/Fidelity.lean)

For Theorem 3.4, `robustness_of_threeCopy_spectrum` assumes a swap-commuting
orthogonal projection on two copies, a nonempty certainty set, and
`spec(S) ⊆ [0,α] ∪ {1}` for `0 ≤ α < 2/3`. It supplies a **single
certainty-state witness** for each unit input. The public theorem applies
to any complex Hilbert space. [Theorem 3.4](manuscript-index.md#r3-4)
· [Spectral statements](../GaussianTesting/GradientFlow/HilbertSpectralGap.lean)

The spaces in Eq. (3.6) are Hilbert completions of algebraic tensor products.
Lean constructs each bounded pair operator by tensoring with the identity
and permuting factors. For example, the matrix element of the 1,2 operator
between `a⊗b⊗c` and `x⊗y⊗z` is
`⟨a⊗b,P(x⊗y)⟩ ⟨c,z⟩`. These matrix elements characterize the operator
because the linear span of elementary cubes is dense. For any Hilbert basis,
the proof identifies the completed square and cube isometrically with the
corresponding product-indexed ℓ² spaces, and identifies the bounded pair
operators with their coordinate actions. The construction permits Hilbert
bases of arbitrary cardinality.
[Tensor completions](../GaussianTesting/GradientFlow/HilbertTensor.lean)
· [Pair matrix elements](../GaussianTesting/GradientFlow/HilbertPairOperators.lean)

For Lemma 3.2, `threeCopyAverage_moments` gives the expectations of `S`
and `S²` on `ψ⊗ψ⊗ψ`. In the expansion of the square, the three diagonal
terms contribute `p` each and the six cross terms contribute `q` each, so
the two moments are `p` and `(p+2q)/3`. For Lemma 3.3, the continuous
functional calculus turns the spectral inclusion for the positive contraction
`S` into nonnegativity of `(S−I)(S−αI)`. Evaluating the quadratic form on
the tensor cube gives `q ≥ p−(3α/2)(1−p)`. Equation (3.5) then yields
`‖∇p‖² ≥ 16(p−3α/2)(1−p)` for the explicit gradient field.
[Moment proof](../GaussianTesting/GradientFlow/HilbertMoments.lean)
· [Functional calculus](../GaussianTesting/GradientFlow/Spectral.lean)
· [Gradient inequality](../GaussianTesting/GradientFlow/HilbertGradientBound.lean)

The footnote immediately before Lemma 3.3 is checked as well: the spectral
inclusion is needed only for the restriction of `S` to `Sym³(H)`. Lean
constructs the closed joint fixed space of the adjacent tensor swaps,
proves that `S` preserves it, and restricts the operator. Positivity,
contractivity, and the two moments on `ψ⊗ψ⊗ψ` pass to this restriction.
The same polynomial-positivity argument then gives the moment and gradient
bounds under this weaker hypothesis.
[Symmetric cube](../GaussianTesting/GradientFlow/SymmetricCube.lean)
· [Restricted spectral bound](../GaussianTesting/GradientFlow/SymmetricCubeGradient.lean)

For every unit input, the fixed-point criterion following Lemma 3.2 says
that `S(ψ⊗ψ⊗ψ) = ψ⊗ψ⊗ψ` if and only if `p(ψ) = 1`. The proof uses the
first moment and the fact that `S` is a contraction. Its complex spectrum
is contained in the real interval `[0,1]`. When the certainty set is
nonempty, a certainty state supplies a nonzero tensor cube with eigenvalue
one, so one is the largest eigenvalue. [Fixed-point and spectrum results](../GaussianTesting/GradientFlow/FixedPoints.lean)

For Eq. (3.4), Lean differentiates the two-copy expectation using the
product rule and swap symmetry. At a unit representative `ψ`, the
centered affine chart sends `v ∈ ψ⊥` to the ray `[ψ+v]`. In this chart
the Fubini–Study speed in direction `v` equals `‖v‖`, and the tangent
metric pairs vectors by the real part of their inner product. Subtracting
`4p(ψ)ψ` from the ambient gradient leaves the unique horizontal vector
whose pairing with each `v` gives the differential. A change of phase
multiplies this vector by the same phase as `ψ`. [Eq. (3.4)](manuscript-index.md#gradient)
· [Lean gradient theorem](../GaussianTesting/GradientFlow/FubiniStudyGradient.lean)

The unnumbered claim following Lemma 3.1 is checked on an arbitrary complete
complex Hilbert space. Lean defines `K_ψ` as `J_ψ† P J_ψ`, where `J_ψ x = x⊗ψ`.
The adjoint agrees with the Riesz contraction already used in the gradient.
Compression preserves positivity, and the unit-vector insertion and the
orthogonal projection have norm at most one. The first two moments equal
`p` and `q`, so Eq. (3.5) also gives the stated variance of `K_ψ`.
In the centered projective chart, Eq. (3.4) identifies the acceptance
differential with the metric dual of `4(K_ψ ψ − p(ψ)ψ)`. Thus that differential
vanishes exactly when `K_ψ ψ = p(ψ)ψ`, as asserted in the manuscript.
[Operator and moments](../GaussianTesting/GradientFlow/Contraction.lean)
· [Projective critical points](../GaussianTesting/GradientFlow/ContractionCriticalPoint.lean)

For Lemma 3.1, `GaussianTesting.projective_gradient_flow` specializes
`TensorSquare.exists_unique_smooth_projectiveFlow` to a swap-commuting
orthogonal projection on the completed Hilbert tensor square. The solution
starts at any prescribed ray of `Projectivization ℂ H` and is smooth in
time in each affine chart through its current ray, with one-sided regularity
at time zero. Uniqueness applies to every curve solving the chart ODE
with the same initial ray and gives equality on `[0,∞)`.
[Projective ODE](../GaussianTesting/GradientFlow/ProjectiveFlow.lean)
· [Lemma 3.1 in Lean](../GaussianTesting/GradientFlow/ProjectiveGradientFlow.lean)

The proof projects a local unit-vector solution of Eq. (3.4) to obtain local
existence on rays. The field is horizontal and equivariant under phase, and
the locally Lipschitz chart field gives uniqueness on overlapping intervals.
This uniqueness identifies an arbitrary projective solution on each closed
subinterval with the projection of a unit-vector solution. For times
`a ≤ b`, energy and Cauchy–Schwarz then give
`d_FS(ρ(a),ρ(b))² ≤ (b−a)(p(ρ(b))−p(ρ(a))) ≤ b−a`.
[Phase and horizontality](../GaussianTesting/GradientFlow/Phase.lean)
· [Energy on rays](../GaussianTesting/GradientFlow/ProjectiveEnergy.lean)

As in the manuscript, a maximal trajectory approaching a finite endpoint is
Cauchy. Lean proves that the Fubini–Study metric on rays induces the quotient
topology and is complete. At the limiting ray a local solution restarts,
and continuity of the chart velocity gives the ODE at the joining time.
Extension past every finite endpoint proves that the maximal forward time
is infinite. [Manuscript continuation proof](manuscript-index.md#r3-1)
· [Complete metric](../GaussianTesting/GradientFlow/FubiniStudy.lean)
· [Projective restart](../GaussianTesting/GradientFlow/ProjectiveContinuation.lean)

For Eq. (3.7), `ray_flow_derivative_bounds` applies to any solution on
`[0,∞)` when `spec(S) ⊆ [0,α] ∪ {1}` and `0 ≤ α ≤ 1`. Write `p_t`
for acceptance along the solution. Its derivative equals the squared norm
of the horizontal gradient. Lean identifies the actual Fubini–Study speed
by taking the limit of distance divided by elapsed time, from the right at
time zero. Its square equals the same derivative. Lemma 3.3 gives the
first inequality, and monotonicity of acceptance gives the second.

\[
  p'_t \ge 16(p_t-3\alpha/2)(1-p_t)
        \ge 16(p_0-3\alpha/2)(1-p_t).
\]

[Ray speed](../GaussianTesting/GradientFlow/RaySpeed.lean) · [Eq. (3.7) in Lean](../GaussianTesting/GradientFlow/RayGradientBound.lean)

The claim immediately after Eq. (3.7) is checked for every projective
trajectory with `3α/2 < p_0 < 1` under the spectral hypothesis. The
upper derivative bound makes `exp(16t)(1-p_t)` nondecreasing, hence
`1-p_t ≥ exp(-16t)(1-p_0) > 0` at every finite time. Equation (3.7)
then gives a positive derivative and strict increase. Acceptance is
bounded by one. If its monotone limit were smaller than one, Eq. (3.7)
would give a uniform positive derivative, contradicting boundedness.
The public conclusion concerns all real forward times. These projective
results now supply the acceptance step in the proof of Theorem 3.4.
[Strict increase and convergence](../GaussianTesting/GradientFlow/RayAcceptanceLimit.lean)
· [Finite-time rejection bound](../GaussianTesting/GradientFlow/RayNonattainment.lean)
· [Continuous-time limit](../GaussianTesting/GradientFlow/RayConvergence.lean)

The subsequent path-length estimate and certainty limit are now checked
for the same arbitrary projective trajectories. A horizontal lift and the
partition estimate for angles bound Fubini–Study distance by integrated
speed on each closed interval. Differentiating the manuscript's potential
`V(p) = ½ arcsin √((1−p)/(1−3α/2))` and applying Eq. (3.7) bounds the
integral by `V(p_s)−V(p_t)`, hence by `V(p_s)`. The chain rule and the
fundamental theorem of calculus implement the manuscript's change of
variables and evaluated integral. Since `p_s → 1` and `V(1)=0`, the
projective trajectory is Cauchy as real time tends to infinity.
Completeness of the Fubini–Study metric yields a limiting ray. Continuity
of ray acceptance gives acceptance one at the limit. Passing the distance
bound to the limit gives `d_FS(ψ_s,ψ_∞) ≤ V(p_s)` for every `s ≥ 0`.
A normalized representative of the limiting ray belongs to the certainty set.
[Projective path length](../GaussianTesting/GradientFlow/RayPathLength.lean)
· [Potential estimate](../GaussianTesting/GradientFlow/RayLength.lean)
· [Certainty limit](../GaussianTesting/GradientFlow/RayTrajectoryLimit.lean)

Theorem 3.4 now uses this projective certainty limit in its proof.
`angular_witness_of_threeCopy_spectrum` starts the global projective flow
from the input ray using Lemma 3.1. For `3α/2 < p(ψ) < 1`, it takes a
normalized representative `φ` of the limiting certainty ray. The identity
`d_FS([ψ],[φ]) = arccos |⟨ψ,φ⟩|` converts the limiting distance estimate
into the angular witness bound. At acceptance one, it takes `φ=ψ`.

`robustness_of_threeCopy_spectrum` derives the linear bound from that
angular witness using the manuscript's estimate
`cos²(½ arcsin √x) = (1+√(1−x))/2 ≥ 1−x` for `x∈[0,1]`.
The same witness satisfies the squared-overlap bound `1−C_α·τ` for every
admissible `τ`; it is chosen before the error parameter. At or below the
threshold this lower bound is nonpositive, so any member of the standing
nonempty certainty set suffices. Comparing the witness overlap with the
supremum fidelity gives the angular and linear fidelity bounds.
[Projective existence](../GaussianTesting/GradientFlow/ProjectiveGradientFlow.lean)
· [Certainty limit](../GaussianTesting/GradientFlow/RayTrajectoryLimit.lean)
· [Theorem 3.4 and its fidelity bounds](../GaussianTesting/GradientFlow/HilbertSpectralGap.lean)

The [manuscript checks](../scripts/ManuscriptChecks.lean) verify that the
public spectral theorem uses projective existence, the path-length estimate,
and the certainty limit.

Informal Theorem 1.2 states the linear consequence for squared class fidelity
and has its own blueprint entry. Since squared fidelity is at least the
witness's squared overlap, `p(ψ) ≥ 1−τ` implies `F² ≥ 1−C_α·τ` for every
`τ ≥ 0`. The public corollary `testing_fidelity_of_threeCopy_spectrum` uses
the same three-copy spectral hypothesis as Theorem 3.4.
[Theorem 1.2](manuscript-index.md#r1-2)
· [Fidelity corollary](../GaussianTesting/GradientFlow/HilbertSpectralGap.lean)

## Kac walk

Theorem 4.1 states both the exact gap `5/12` for the Kac transition operator on
`L²(S²)` and spectral containment for every strongly continuous unitary
representation of `SO(3)`. The manuscript computes the Gram matrix of the three
axis-invariant lines in each nontrivial irreducible representation. The largest
nontrivial eigenvalue, `7/12`, occurs at spin four. Lean now checks the exact
intermediate calculation: the alternating binomial-square formula for the
overlap, its odd/even closed forms, the two nonzero Gram eigenvalue branches,
their actual maximum, and the strict bound below `7/12` for integer spins
`j ≥ 6`. The weight basis supplies concrete coordinates for the manuscript's
irreducible representations. The public gap proof derives its quadratic-form
bound from this exact maximum. The arbitrary-representation
extension now follows the manuscript's decomposition route: compact-group Haar
averaging gives finite invariant subspaces and a dense span of irreducibles;
the axis actions yield the angular-momentum generators and their fixed-space
kernels. Restriction preserves the projections, and the uniform quadratic-form
bound extends by continuity. The resulting theorem gives the literal spectral
inclusion without finite-dimensional or separability assumptions.

The Kac preliminaries now construct the natural sphere representation.
The underlying space is the actual unit sphere in Euclidean real three-space;
its measure is normalized `volume.toSphere`. Invariance follows from the
radial-cone definition of surface measure and preservation of Euclidean volume
by rotations. Inverse pullback defines the complex unitary representation,
with its almost-everywhere formula and group law. Continuity of composition
by continuous measure-preserving maps proves strong continuity for every
`L²` vector. Uniform vector-valued circle integration now gives each
axis-invariant orthogonal projection: periodicity proves invariance, and
pairing with fixed vectors characterizes the projection. On continuous sphere
observables, the average of these integrals is exactly uniform axis/angle
sampling. Reflection of the full-period integral identifies inverse pullback
with the usual forward-rotation formula. Continuous observables are dense in
`L²`, so this formula has a unique bounded extension, proved equal to the
projection average. These preliminaries support the precise spherical-gap calculation.
[Sphere measure](../GaussianTesting/Kac/SphereMeasure.lean)
· [Sphere representation](../GaussianTesting/Kac/SphereRepresentation.lean)
· [Circle averages](../GaussianTesting/Kac/AxisAverage.lean)
· [Kac transition](../GaussianTesting/Kac/SphereKacTransition.lean)

The identification of the trivial component with constants is now checked
under Theorem 4.1. Equality in the projection norm bounds shows that the
average fixes a vector exactly when all three axes do. Coordinate-plane
generation gives invariance under SO(3). Its sphere action is transitive,
so normalized Haar averaging makes every continuous observable constant.
The vector-valued averaging operator is bounded; density and closedness of
the constant subspace extend this conclusion to L². Invariant vectors equal
their averages. Thus the eigenvalue-one space is exactly the span of `1`,
equivalently the functions constant almost everywhere.
[Fixed space](../GaussianTesting/Kac/SphereFixedSpace.lean)

The restriction to the orthogonal complement of constants now has a checked
norm bound `7/12`. On each finite invariant subspace, eigenvalue one is
excluded by the fixed-space result; the general spectral inclusion therefore
gives the norm bound. Density extends it to the full complement.

For the manuscript’s spin-four attainment, Lean uses the explicit zonal
functions `h_a(x) = P₄(x_a) = (35 x_a⁴ − 30 x_a² + 3)/8`. Their ambient
quartic extensions are proved homogeneous of degree four with vanishing
polynomial Laplacian. Their own-axis averages fix them, while a different
axis average sends `h_a` to `(3/8)h_b`, realizing the manuscript’s `a₄=3/8`
matrix. Their sum has eigenvalue `7/12`, and its pole value `7/4` together
with full support of sphere measure proves it is nonzero in L². Symmetry
makes it orthogonal to constants. The restricted norm and largest spectral
value are therefore exactly `7/12`, proving the gap `5/12`. This concrete
harmonic realization supplies the needed attainment without developing a
classification of all spherical harmonics.
[Upper bound](../GaussianTesting/Kac/SphereGapBound.lean)
· [Harmonic polynomial certificates](../GaussianTesting/Kac/SphereHarmonicQuartic.lean)
· [Axis projection matrix](../GaussianTesting/Kac/SphereSpinFour.lean)
· [Exact gap](../GaussianTesting/Kac/SphereGap.lean)
[Theorem 4.1](manuscript-index.md#r4-1)
· [General spectral inclusion](../GaussianTesting/Kac/GeneralRepresentation.lean)

## Gaussian states

The bosonic preliminaries now construct the Weyl operators on actual
`L²(ℝᵐ)` from the explicit action
`D_(q,p) f(x) = exp(i pᵀ(x−q/2)) f(x−q)`, as agreed with the authors.
Translation invariance of Lebesgue measure and the unit-modulus multiplier
give unitarity, the Weyl composition law, and the adjoint `D_(−q,−p)`.
Translation continuity and dominated convergence for modulation give strong
continuity and joint continuity in the parameter and input wavefunction.
The characteristic function `Tr(ρ D_r)` is basis independent, continuous,
equals one at zero for density operators, has modulus at most one, and
satisfies `χρ(−r) = conj(χρ(r))`. The trace proofs use the established
summable Gram representation. The vacuum characteristic function and its
displaced form are checked by the Gaussian Fourier integral. Characteristic-function
injectivity is checked for pure states, by Fourier uniqueness and correlation kernels,
without moment or regularity assumptions. Injectivity for arbitrary mixed states remains unused. The required pure Gaussian
characteristic-function identification with the physical vacuum orbits is checked. The manuscript retains the equivalent
unbounded-exponential notation as background; its identification with the
explicit action is not used or proved in Lean.
[Weyl operators](../GaussianTesting/Bosons/Weyl.lean)
· [Strong continuity](../GaussianTesting/Bosons/WeylContinuity.lean)
· [Characteristic functions](../GaussianTesting/Bosons/CharacteristicFunction.lean)
· [Vacuum formula](../GaussianTesting/Bosons/VacuumCharacteristic.lean)
· [Pure-state injectivity](../GaussianTesting/Bosons/CharacteristicInjectivity.lean)

Weyl covariance under copy rotations is proved on actual wavefunctions and
on the completed tensor square, including the manuscript’s balanced
difference/sum formula in Eq. (6.4). Orthogonal matrices act on any number of copies by
inverse coordinate pullback. This gives an actual unitary representation,
jointly continuous in the matrix and input; its special-orthogonal restriction
is checked and its two-copy plane rotations equal `Uθ` from Eq. (6.1).
Periodic averaging now proves the converse: a rotation-fixed vector belongs to
the prescribed closed kernel. Polynomial Gaussian orbits lie in finite-dimensional
spaces; averaging stays on the finite core and has zero generator. Density and
graph closure extend this to arbitrary fixed vectors.

The number vectors are a complete orthonormal basis. Creation/annihilation
adjointness by Gaussian integration by parts and the commutator give their
orthogonality and factorial norms; polynomial Gaussian density gives completeness.
The resulting unitary maps occupation coefficients to actual wavefunctions,
intertwines the finite and closed two-copy generator graphs and kernel projections,
and respects completed product tensors.
[Number basis](../GaussianTesting/Bosons/SchrodingerNumberBasis.lean)
· [Closed-generator transport](../GaussianTesting/Bosons/SchrodingerFockPair.lean)
· [Tensor products](../GaussianTesting/Bosons/NumberTensor.lean)
· [Fixed space and kernel](../GaussianTesting/Bosons/RotationFixedSpace.lean)

Actual symplectic unitaries are constructed from quadratic phases, normalized
coordinate changes, Fourier transform, and a symplectic block decomposition.
For every real symplectic matrix, the manuscript's inverse Weyl covariance holds;
identical copies commute with rotations and the closed-kernel projection. These
are the action properties used in Section 6. Projective/metaplectic structure,
ground-state equivalences, and exponential identifications are not required targets.
[Symplectic action](../GaussianTesting/Bosons/SymplecticAction.lean)
· [Kernel invariance](../GaussianTesting/Bosons/GaussianKernel.lean)
[Displacement covariance](../GaussianTesting/Bosons/WeylRotation.lean)
· [Actions on copies](../GaussianTesting/Bosons/SchrodingerCopies.lean)

The fermionic operator `lambdaF` has the manuscript's Majorana normalization.
The library uses the Jordan–Wigner representation and includes states in both
parity sectors. A state belongs to `IsGaussian` if it is obtained from an
occupation basis vector of either parity, up to phase, by a finite product of
unitaries implementing rotations in Majorana coordinate planes. Theorem 5.2
gives a witness in the independent even/odd Gaussian orbit union with squared
overlap at least `1−8τ` and the same lower bound on squared class fidelity.
The orbit union’s identification with `IsGaussian` is checked.
[Fermionic definitions](../GaussianTesting/Fermions/Gaussian.lean)
· [Testing bound](../GaussianTesting/Fermions/Robustness.lean)

Lemma 5.1 now follows the manuscript's proof. A general real antisymmetric
normal-form theorem supplies a special orthogonal block diagonalization.
Gaussian covariance transport preserves the squared Hilbert–Schmidt norm;
the covariance identity then forces every expectation of `2N_k−I` to be ±1,
so the transformed state is an occupation vector up to phase. The public
theorems `fermionicGaussian_iff_lambdaF` and `fermionicGaussian_iff_accProb`
identify the independent Gaussian orbit union with the kernel condition and
perfect acceptance for every unit input. They impose neither a parity
restriction nor a positive-mode hypothesis. The `isGaussian_*` interfaces
are aliases to this argument, replacing the previous successive-row reduction.
[Lemma 5.1](../GaussianTesting/Fermions/GaussianCertainty.lean)
· [Antisymmetric normal form](../GaussianTesting/Fermions/SkewNormalForm.lean)
· [Covariance transport](../GaussianTesting/Fermions/CovarianceAction.lean)
· [Occupation saturation](../GaussianTesting/Fermions/CovarianceOccupation.lean)

The implementer construction uses the manuscript's Majorana action as its
independent specification. Every real special orthogonal matrix is a product
of coordinate-plane rotations, whose explicit half-angle unitaries give
`exists_gaussianImplementer`. The public conjugation theorem is Eq. (5.1).
Commuting with every Majorana forces a scalar linear map, so two implementers
of the same rotation differ by a unit phase. All implementers preserve parity.
Paired occupation flips prove transitivity on basis vectors of a fixed parity,
and `fermionicGaussianStates_eq_isGaussian` identifies the union of the two
independent orbits with the existing coordinate predicate. The odd zero-mode
class is empty. None of these background proofs invokes Lemma 5.1.
[Implementers and phase uniqueness](../GaussianTesting/Fermions/GaussianImplementers.lean)
· [Even and odd orbits](../GaussianTesting/Fermions/GaussianOrbits.lean)

Creation and annihilation now reconstruct the prescribed Majoranas, their
product is the diagonal occupation number operator, and `i c_X c_Y = 2N−I`
is checked. The two formulas for `Λ`, its conjugation invariance under every
Gaussian implementer (Eq. (5.2)), and acceptance invariance are also checked.
[Occupation operators and the ladder formula](../GaussianTesting/Fermions/CreationAnnihilation.lean)
· [Gaussian test invariance](../GaussianTesting/Fermions/GaussianTestInvariance.lean)

The required second-quantized action is checked. Normalizing a passive real
Gaussian implementer to fix the vacuum gives a strongly continuous unitary
representation. The exterior-algebra/occupation equivalence identifies this
action exactly with the exterior power of the one-particle rotation on each
particle-number sector. The three-copy occupation identification and the
mode matrix `R ⊗ I_m` then give the manuscript’s representation and its exact
Majorana parity strings.
[Second quantization](../GaussianTesting/Fermions/SecondQuantization.lean)
· [Exterior-power action](../GaussianTesting/Fermions/ExteriorOccupation.lean)
· [Copy coordinates](../GaussianTesting/Fermions/CopyCoordinates.lean)
· [Copy representation](../GaussianTesting/Fermions/CopyRepresentation.lean)

Theorem 5.2 now uses that representation to identify the three axis-fixed
spaces with the pair-test kernels. The generator normalization and axis
orientations are proved; the common nonzero scalar does not change their
kernels. Thus `S = T_π`, and the general Kac theorem supplies the complex
spectral inclusion in `[0,7/12] ∪ {1}`. The finite-coordinate bridge invokes
the completed-tensor projective proof of Theorem 3.4. Lemma 5.1 identifies its
certainty witness with the independent Gaussian class, and the supremum
fidelity bounds that witness’s overlap. The public theorems
`fermionic_fidelity_witness` and `fermionic_fidelity` assume only unit norm
and the acceptance bound; nonnegativity of `τ` is inferred. They include zero
modes.
[Axis projections and spectrum](../GaussianTesting/Fermions/CopyKac.lean)
· [Completed-tensor bridge](../GaussianTesting/GradientFlow/FiniteHilbert.lean)
· [Theorem 5.2](../GaussianTesting/Fermions/Robustness.lean)

The fermionic preliminaries node is complete for the background this proof
needs. The ordered Majorana-product parity formula and standalone two-copy
`SO(2)` interpretation are now checked too. The actual occupation unitary
transports the two parity strings and CAR, and differentiating the real
second-quantized action gives `iL/2`; its full invariant space is `ker Λ`.
The unused full complex `SU(m)` action remains outside the checked scope.
The checked three-copy action is indexed separately. Corollary 5.3 is
checked for the pair-projection protocol. Figure 1(a)'s Bell measurement
implements this projection with the explicit classical rule described below.

The single fermionic preliminaries node owns the required occupation and
Jordan–Wigner formulas, CAR, parity, number basis, `SO(2m)` implementers
and orbit classes, and the reusable parity-string and second-quantization
facts. The simultaneous Gaussian invariance of the particular test belongs to
its definition node. The covariance norm calculation and saturation argument
belong to Lemma 5.1: the paper cites the fixed-parity characterization but
proves the version without a parity assumption. The concrete rotation-generator
identities, kernel-projection identification and `S = T_π` remain proof steps
of Theorem 5.2, now checked for the actual second-quantized action.
Corollary 5.3 owns the checked fermionic application of the generic repetition
law and copy bounds. `fermionicTestProtocol` uses independent fresh pairs,
each measured with `P_F`, and accepts exactly when all rounds accept.
`fermionic_testing` proves perfect completeness from Lemma 5.1 and soundness
from Theorem 5.2: `F² ≤ 1−ε²` implies `p ≤ 1−ε²/8`, hence `pⁿ ≤ δ`
for `n = ⌈(8/ε²) log(1/δ)⌉`. Its exact copy count is `2n`, bounded by
`16 ε⁻² log(1/δ) + 2` for every `0 < ε,δ < 1` and by
`32 ε⁻² log(1/δ)` when `δ ≤ exp(−1)`. The promise uses the manuscript's
supremal fidelity with the independent Gaussian orbit class directly.
[Fermionic protocol](../GaussianTesting/Fermions/Testing.lean)
· [Product law and copy bounds](../GaussianTesting/RepeatedTest.lean)

The cited fermionic kernel-span and symmetric-support statements are checked
for both Gaussian parity classes. The proof uses their invariant span, the
one-dimensional joint Bell eigenlines, a vacuum-square overlap, and signed
Majorana-coordinate permutations. The manuscript now specifies twirling over
the full orthogonal group, which includes both parity orbits. Lean retains the
previously agreed direct spanning argument; it does not assert a separately
formalized Haar-twirling identity. The stated span equality is unchanged. A general positive-contraction argument
then proves that `P_F` has minimal acceptance among all perfectly complete
two-copy effects, even on arbitrary two-copy vectors. The shared introductory
span/optimality node now also includes the full bosonic closed-span equality
and its optimality application.
[Span proof](../GaussianTesting/Fermions/GaussianSquareSpan.lean)
· [Optimality](../GaussianTesting/Fermions/PerfectCompleteness.lean)

For bosons, the closed span of centered Gaussian squares is exactly the
symmetric part of the actual closed-generator kernel, on full `L²` and
including zero modes. Rotation/swap averaging preserves polynomial Gaussians.
In complex coordinates the invariant polynomials are balanced and swap-fixed;
finite-dimensional duality proves that they are generated by the Gram
quadratics. Differentiating quadratic Gaussian phases puts their polynomial
multiples in the closed square span. Density completes the equality without
any moment assumption on arbitrary kernel vectors. Since `P₀` commutes with
swap, its action on identical inputs equals that span projection. The general
positive-contraction comparison proves optimality for the actual test, with
no swap-invariance assumption on a competing effect. The manuscript's
``measures exactly the span'' wording is preserved in this two-copy context.
[Bosonic span](../GaussianTesting/Bosons/GaussianSquareSpan.lean)
· [Bosonic optimality](../GaussianTesting/Bosons/PerfectCompleteness.lean)

The manuscript's expanded Howe and Kashiwara–Vergne commutant discussion
remains unused background, as do the spin double-cover and quadratic-ground-state
equivalences. The general bosonic `O(t)` action is already checked in copy-first
coordinates `Fin t × Fin m`, with the inverse pullback prescribed in Section 6.
The fermionic `SO(2)` and `SO(3)` actions suffice for the tested results; the
full fermionic `O(t)` action and the abstract general second-quantization
identifications are not prerequisites to those proofs.

The physical bosonic development uses actual `L²(ℝᵐ)` wavefunctions and the
manuscript's symplectic-vacuum and displaced-vacuum orbit descriptions as
independent state sets. The supporting coefficient model is `ℓ²` over occupation
vectors and supplies the finite-particle calculations used by the physical proofs.
A Gaussian characteristic function is now proved to give the corresponding orbit,
without extra moment or covariance assumptions. Coherent states are defined as
displaced vacua, and the physical coherent test characterizes that class up to global phase.
Ground-state and explicit mean-operator equivalences are unused
and not asserted. The prescribed graph-norm closure of the finite Fock
generator is now explicit, and its coordinate kernel projection equals `P0B`.
The physical Schrödinger realization independently closes the graph of the
creation-annihilation expression on the actual finite number-vector span.
Its closed-kernel projection is `schrodingerP0`. The actual number-basis unitary now intertwines these closed generators
and their kernel projections, the balanced splitters, and the coherent projections.
Lemma 6.2 is proved directly in the wavefunction model. [Physical definitions and domain](manuscript-index.md#lambda-b)
· [Fock-space kernel projection](../GaussianTesting/Bosons/Main.lean)
· [Gaussian state classes](../GaussianTesting/Bosons/GaussianWaveStates.lean)

| Manuscript result | Lean conclusion |
|---|---|
| Proposition 6.3 | `bosonicGaussian_and_coherent_characterization` gives both physical certainty equivalences for the independent Gaussian and coherent vacuum orbits. The Gaussian converse follows the manuscript's purity reduction. |
| Theorem 6.4 | `schrodinger_meanZero_fidelity_witness` gives a physical centered Gaussian witness whose squared overlap lies between `1−8τ` and squared fidelity with `meanZeroGaussianWaveStates`. The physical pair average is exactly the SO(3) Kac operator, so the proof uses Theorems 4.1 and 3.4 as in the manuscript. |
| Theorem 6.5 | `schrodinger_coherent_fidelity_witness` gives a physical coherent witness whose squared overlap lies between `1−4τ` and the squared fidelity with the displaced-vacuum class `coherentWaveStates`. `schrodinger_coherent_fidelity` gives the manuscript's fidelity bound. |
| Lemma 6.6 | `schrodinger_coherent_spectrum_subset` proves the spectral inclusion `[0,1/2] ∪ {1}` on the actual completed wavefunction tensor cube, using the proved number-basis identification with `coherent_spectrum_subset`. |
| Theorem 6.7 | `schrodinger_gaussian_fidelity_witness` gives a physical Gaussian witness with squared overlap at least `1−48τ`, following the manuscript's quantitative purity reduction and symplectic/coherent transport. `schrodinger_gaussian_fidelity` gives the same bound for squared fidelity with `gaussianWaveStates`. |
| Corollary 6.8 | `bosonic_physical_testing` constructs the physical independent product protocol with perfect completeness, squared-fidelity soundness and the integer copy count. `testingCopies_le_rate` supplies the explicit asymptotic bound. |

Proposition 6.1 is complete on actual wavefunctions. Its proof follows the manuscript from the
closed kernel to the balanced characteristic-function equation (6.3), strict positivity,
the parallelogram law for its logarithm, and polarization to a continuous nonpositive
quadratic form. The forward symplectic-vacuum-orbit implication is checked using
the finite vacuum kernel and Gaussian invariance. The Gaussian-characteristic reconstruction now completes the public three-way
equivalence in `bosonicMeanZeroGaussian_characterization`: physical orbit membership,
closed-generator kernel membership, and acceptance one. The only hypothesis is unit
norm; kernel membership includes the prescribed domain. The Gaussian set uses the
manuscript independent symplectic-vacuum description. These proof steps belong to Proposition 6.1.
[Physical characteristic argument](../GaussianTesting/Bosons/MeanZeroCharacteristic.lean)
· [Positivity and polarization](../GaussianTesting/Bosons/CharacteristicEquation.lean)

Both halves of Proposition 6.3 are checked on actual wavefunctions.
For the Gaussian converse, the actual reduced-state trace and Lemma 6.2 force
the reduced operator to have norm one. It is rank one; product factorization
and Proposition 6.1 identify its right factor as a centered Gaussian.
The inverse symplectic unitary on both copies turns this factor into the vacuum,
reducing to coherent certainty. Weyl covariance transports the input back to
the independent displaced Gaussian orbit. The forward implication uses the
manuscript's displaced Gaussian splitter factorization and the retained factors.

For coherent states,
Unit acceptance gives a vacuum factor after the inverse balanced splitter.
Dividing by the vacuum characteristic function gives Eq. (6.7) and a continuous unit-circle
character, hence a symplectic linear phase. Pure-state injectivity identifies a
Weyl-displaced vacuum; vacuum rotation invariance and Weyl covariance give the
forward implication. This proof is recorded under Proposition 6.3.
[Physical Gaussian equivalence](../GaussianTesting/Bosons/PhysicalGaussian.lean)
· [Purity reduction](../GaussianTesting/Bosons/GaussianPurityReduction.lean)
· [Symplectic reduction](../GaussianTesting/Bosons/GaussianSymplecticReduction.lean)
[Physical coherent equivalence](../GaussianTesting/Bosons/PhysicalCoherent.lean)
· [Normalized characteristic equation](../GaussianTesting/Bosons/CoherentCharacteristic.lean)

Theorem 6.5 is complete on actual wavefunctions. Its proof follows the
manuscript directly: Lemma 6.6 gives the spectral inclusion with `α = 1/2`,
Proposition 6.3 identifies the certainty set with displaced vacua, and
Theorem 3.4 supplies a coherent witness and the constant `4`. The squared
overlap is bounded above by the manuscript's supremal squared fidelity.
Only unit norm and `q(ψ) ≥ 1 − τ` are hypotheses; nonnegativity of `τ` is
derived from the probability bound.
[Physical coherent robustness](../GaussianTesting/Bosons/PhysicalCoherentRobustness.lean)

Lemma 6.6 now uses the manuscript's exact three-direction Gram calculation.
The revised notation is reflected in `vVec`, the uniform vector `v`, and
`wVec a`, whose normalization is the manuscript's `w_ab`. The rotated occupation
labels put the center direction `V = ℂv` first and its complement `W` second,
exactly as in the manuscript's unnumbered Fock decomposition. Within a label of complementary degree `k`, the overlaps are
`s = (−1/2)^k`, and the nonzero spectral values are exactly `(1+2s)/3` and
`(1−s)/3`. The maxima are `1` for `k=0`, `1/2` for `k=1,2`, and strictly
less than `1/2` for `k≥3`. The public proof sums the resulting quadratic
inequality over the particle-number blocks. It proves that the
average of the three pair projections is a positive contraction and applies
the spectral equivalence on the full Fock space. The number-basis, tensor,
splitter and vacuum-projection identities now identify its spectrum with that
of the actual three-pair average on the physical completed tensor cube.
[Coherent spectrum](../GaussianTesting/Bosons/CoherentSpectrum.lean) · [Manuscript checks](../scripts/ManuscriptChecks.lean)

Theorem 6.7 uses the same quantitative reduction as the expanded manuscript
proof. Equation (6.8) is the top-eigenvalue estimate in
`schrodingerReducedState_top_eigenstate`; Eq. (6.9) applies
`schrodinger_meanZero_fidelity_witness` to that eigenstate.
`schrodingerReducedState_covariance` now states the displayed operator equality
`σ = U_S ρ U_S†`, obtained from the existing diagonal matrix coefficients by
polarization. The coherent reduction uses this operator equality directly.
The basic acceptance-invariance assertion after Eq. (6.2) is exported separately
as `schrodingerMeanZeroAcceptance_symplectic`; this uses the checked kernel
projection covariance and does not assert full unbounded-generator conjugation.
[General Gaussian robustness](../GaussianTesting/Bosons/PhysicalGeneralRobustness.lean)
· [Mean-zero acceptance invariance](../GaussianTesting/Bosons/PhysicalMeanZero.lean)

Lemma 6.2 is fully proved by `purity_schrodinger` for every positive
trace-class operator of trace one on actual `L²(ℝᵐ)`. A Hilbert basis is used
only to define diagonal sums: the density criterion and the complex observable
trace are proved basis independent. The positive-square-root construction
`g_i = sqrt(ρ) e_i` supplies a normalized summable Gram representation, and
Parseval's identity gives equality of its Gram operator with `ρ`. Absolute
double-sum interchange identifies the complex operator trace with the family
expectation, including for the non-self-adjoint signed-swap observable.

The two-copy density is `T(ρ⊗ρ)T†`, where `T` sends elementary tensors to
actual products of wavefunctions. Fubini proves that `T` is isometric and
that this operator has trace one. Surjectivity is unnecessary for these
product states. The physical generator acts by the manuscript's
creation-annihilation expression on finite linear combinations of the specified
number vectors. Its graph closure is an operator; the integrated rotation
identity passes to the closure and proves that rotations fix its kernel.
Thus its kernel projection is the actual test used in the theorem.

The proof follows all three displayed steps in the manuscript:
`2 Tr(P₀ρ⊗ρ) − 1 ≤ Re Tr(Uπ/2 ρ⊗ρ)`,
`Tr(Uπ/2 ρ⊗ρ) = Tr(Jρ²)`, and
`|Tr(Jρ²)| ≤ Tr(ρ²) ≤ ‖ρ‖`.
Cyclicity supplies the product order in the hypothesis. The acceptance trace
is real, with real part in `[0,1]`, so its real-part comparison is exactly the
probability hypothesis. The theorem assumes
neither a Gram family nor a moment or intertwining condition.
The physical reduced state and four-copy measurement are constructed directly,
and the quantitative reduction uses their checked trace identities.
[Physical purity theorem](../GaussianTesting/Bosons/SchrodingerPurity.lean)
· [Hilbert-space density and trace](../GaussianTesting/Bosons/HilbertDensity.lean)
· [Signed-swap trace proof](../GaussianTesting/Bosons/SignedSwapPurity.lean)
· [Physical graph closure](../GaussianTesting/Bosons/SchrodingerLambda.lean)

## Measurements and sample complexity

Figure 1(a) is checked in the manuscript's Jordan–Wigner coordinates. The
product Bell basis has local vectors
`(|0,b_k⟩ + (−1)^a_k |1,¬b_k⟩)/√2`, and its unitary coordinate transform
is the Bell readout. The eigenvalue of `Λ` is
`2∑_{k:b_k=1}(−1)^(a_k+∑_{j<k}b_j)`, including the prefix parity from
the Jordan–Wigner strings. The classical rule accepts exactly when this
integer is zero. `fermionicBellMeasurement_eq_PF` identifies the pulled-back
diagonal outcome projection with `P_F` on the entire two-copy space.
`fermionicBellMeasurement_acceptance` gives its Born expectation, and
`fermionicBellReadout_probability` equates the sum of accepted Bell-outcome
probabilities with `accProb (PF m) ψ`. The statement includes zero modes and
does not assume a parity sector. This implements the corollary's one-round
measurement; the repeated protocol and sample complexity remain in Corollary 5.3.
[Figure 1(a) readout](../GaussianTesting/Fermions/BellMeasurement.lean)
· [Bell basis](../GaussianTesting/Fermions/BellBasis.lean)
· [Bell eigenvalues](../GaussianTesting/Fermions/BellEigenvalues.lean)

The physical coherent projection is constructed as
`Q = U(I⊗|0⟩⟨0|)U†` on completed copies of actual wavefunctions. The
normalized Gaussian vacuum is fixed by reflection. Direct coordinate
calculation gives `S U = U(I⊗J)`, hence `SQ = Q = QS`. Its Born expectation
is real, lies in `[0,1]` for unit inputs, and equals the vacuum trace of the
reduced state after the inverse rotation. `QB_eq_conj` separately proves the
conjugated-vacuum identity in Fock coordinates. The number-basis unitary now
identifies the two projections. Figure 1(c)'s physical number readout is checked:
zero total occupation is exactly the vacuum outcome, and the pulled-back
accepting projection is `Q` with Born probability `schrodingerCoherentAcceptance`.
[Coherent projection](../GaussianTesting/Bosons/SchrodingerCoherent.lean)
· [Normalized vacuum](../GaussianTesting/Bosons/SchrodingerVacuum.lean)
· [Figure 1(c) readout](../GaussianTesting/Bosons/CoherentMeasurement.lean)

Figure 1(b) is also checked on actual wavefunctions. The phase on register two
is `(-i)^N` in the proved oscillator basis. Its composition with the positive
balanced splitter sends the equal-total-number projection to
`schrodingerTensorP0`; the Born probability is `schrodingerMeanZeroAcceptance`.
The manuscript's signed number-difference identity holds on the finite core,
and the transformed number eigenvectors and their dense span identify the full
bounded accepting projection.
[Figure 1(b) readout](../GaussianTesting/Bosons/MeanZeroMeasurement.lean)

The general four-copy projection is constructed independently of
its trace formula: undo the balanced rotation on pairs 12 and 34, regroup as
(13)(24), and apply the physical `P₀` to registers 24. Symmetry and idempotence
are proved. Finite-rectangle density makes the wavefunction tensor map unitary.
The inverse-rotation output has a basis-independent partial trace, characterized
against every bounded observable. Its two-copy reduced operator is `ρ⊗ρ`, giving
Eq. (6.5)'s complex expectation identity and acceptance in `[0,1]`.
The analogous vacuum expectation for the coherent test is Eq. (6.6), proved by
`schrodingerCoherentAcceptance_eq_vacuumExpectation`.
[Physical four-copy test](../GaussianTesting/Bosons/SchrodingerFourCopy.lean)
· [Partial trace](../GaussianTesting/Bosons/PartialTrace.lean)

Figure 1(d) uses negative-angle splitters on both pairs and retains outputs
two and four, exactly as in §6. `fourCopyFigurePreparation_eq` identifies the
preparation on the entire four-copy Hilbert space. Combining it with panel (b)'s
physical readout gives `fourCopyNumberMeasurement_eq_projection`, equality with
the Section 6 accepting operator on arbitrary inputs. Its Born probability on
four identical inputs is therefore `schrodingerFourCopyAcceptance`. The separately indexed introductory
claims about parity and first moments of the difference output are now checked
in their own node. The output has even Gram columns and even reduced range.
Global position/Fourier densities are identified by bounded-event traces, and
their global coordinate integrability implies zero position/momentum means.
This first-moment hypothesis also implies each columnwise hypothesis; it is
not merely a sum of potentially undefined component moments.
[Figure 1(d) readout](../GaussianTesting/Bosons/FourCopyMeasurement.lean)
· [Figure 1 circuits](coverage.md#figure-1-circuits)

The one-round acceptance deficit is `τ`. Corollaries 5.3 and 6.8 use the squared-fidelity
promise `F² ≤ 1−ε²` directly. `fermionic_testing` and `bosonic_physical_testing`
construct product probability laws for independent fresh-copy rounds with the one-round
Born acceptance probability `p`. The event that all rounds accept has
probability `pⁿ`. The physical certainty characterizations give perfect
completeness, and the fidelity bounds imply rejection probability at least
`1−δ` for a far input.

For general, mean-zero and coherent bosonic states, respectively,
`(k,C) = (4,48), (2,8), (2,4)`; for fermionic Gaussian states,
`(k,C) = (2,8)`. The protocol uses exactly
`k⌈(C/ε²) log(1/δ)⌉` copies. For all `0 < ε,δ < 1`, this is at most
`kC ε⁻² log(1/δ) + k`. For `δ ≤ exp(−1)`, the checked explicit bound is
`2kC ε⁻² log(1/δ)`, proving the stated Big-O rate in that regime. The uniform
bound retains the additive `k` as `δ` approaches one.
[Physical bosonic protocol](../GaussianTesting/Bosons/PhysicalTesting.lean)
· [Fermionic protocol](../GaussianTesting/Fermions/Testing.lean)
· [Product law and copy bounds](../GaussianTesting/RepeatedTest.lean)

Theorem 1.1 now has public statements with the manuscript's pointwise promise
and with trace distance at least `ε` from every Gaussian state.
`fermionic_gaussian_testing` and `bosonic_gaussian_testing` use the proved
equivalence between pointwise squared-overlap bounds and the supremal
class-fidelity bound. Their trace-distance versions use the identity
`½‖|ψ⟩⟨ψ|−|φ⟩⟨φ|‖₁ = √(1−|⟨φ,ψ⟩|²)` and keep the same protocols and
integer copy counts.

Here the trace norm is defined as the trace of `|A| = √(A†A)`.
For the difference of unit-vector projectors, Lean
proves positive trace class of the modulus and independence of the Hilbert
basis. The rank-one calculation gives `A³=(1−|⟨φ,ψ⟩|²)A`; uniqueness of
the positive square root and the trace of `A²` then give the identity.
The coincident-ray case is included. The argument applies to arbitrary complex
Hilbert spaces, so the bosonic result has no finite-dimensional restriction.
[Trace norm and distance](../GaussianTesting/TraceDistance.lean)
· [Rank-one difference calculation](../GaussianTesting/PureStateDifference.lean)
· [Theorem 1.1 interfaces](../GaussianTesting/Testing.lean)

The independent fermionic Gaussian orbit class is identified with `IsGaussian`,
and Lemma 5.1, Theorem 5.2, Corollary 5.3, and Figure 1(a) are checked.
[Testing statement](manuscript-index.md#r1-1)
· [Fermionic sample complexity](manuscript-index.md#r5-3)
· [Bosonic sample complexity](manuscript-index.md#r6-8)
· [Coverage and remaining scope](coverage.md)

Pure-state density correspondence is checked in the bosonic preliminaries: a
rank-one positive operator has trace equal to the squared vector norm; unit
projectors coincide exactly up to phase. Idempotent density operators are
exactly unit-vector projectors and correspond to unique projective rays.
[Pure-state density interface](../GaussianTesting/Bosons/PureStateDensity.lean)
· [Difference-output parity and global moments](../GaussianTesting/Bosons/DifferenceParity.lean)
