# Formalization coverage

All **18 numbered results** in [the manuscript](../material/manuscript.tex)
and all four measurement circuits in Figure 1 are formalized. The proofs use
independently defined Gaussian state classes and the physical Hilbert spaces.
The [manuscript index](manuscript-index.md) gives exact statements, source
locations, Lean declarations, proof routes, and qualifications for each item.
The [comparison report](manuscript-comparison.md) explains the mathematical
correspondence in detail.

## Results

| Manuscript | Checked content |
| --- | --- |
| [Theorems 1.1–1.2](manuscript-index.md#r1-1) | Gaussian testing with mode-independent copy bounds; robustness from the three-copy spectral gap. |
| [Lemmas 3.1–3.3 and Theorem 3.4](manuscript-index.md#r3-1) | Smooth unique projective flow on arbitrary complex Hilbert spaces, tensor-cube moment identities, gradient bounds, and angular and linear fidelity bounds. |
| [Theorem 4.1](manuscript-index.md#r4-1) | The Kac bound for every strongly continuous unitary representation of SO(3), and the exact spherical gap 5/12. |
| [Lemma 5.1, Theorem 5.2, Corollary 5.3](manuscript-index.md#r5-1) | Fermionic Gaussian characterization, fidelity bound, and repeated-test sample complexity. |
| [Propositions 6.1 and 6.3, Lemma 6.2](manuscript-index.md#r6-1) | Bosonic exactness and the purity bound for arbitrary positive trace-class operators of trace one. |
| [Theorems 6.4, 6.5 and 6.7, Lemma 6.6, Corollary 6.8](manuscript-index.md#r6-4) | Physical bosonic fidelity bounds, the coherent-test spectrum, and repeated-test sample complexity. |

## Figure 1 circuits

Each circuit's accepting operator is identified on its full input space.

| Panel | Readout and accepting operator |
| --- | --- |
| [(a) Fermions](manuscript-index.md#f1a) | Bell measurement and classical postprocessing give `PF`. |
| [(b) Mean-zero bosons](manuscript-index.md#f1b) | Phase shift, beam splitter, and equal total particle counts give `schrodingerTensorP0`. |
| [(c) Coherent states](manuscript-index.md#f1c) | The zero-number output of a balanced splitter gives `schrodingerQ`. |
| [(d) General bosons](manuscript-index.md#f1d) | Two negative-angle splitters, retained outputs (2,4), and panel (b)'s readout give `schrodingerFourCopyProjection`. |

The introductory Gaussian-square span and optimality claims, pure-state
trace-distance identity, and difference-output parity and first-moment claims
are also checked. First moments are asserted only when they exist.

## Scope qualifications

The manuscript assumes at least one mode. Lean's results also cover zero modes
where stated. Robustness and testing concern normalized pure inputs; the
purity lemma separately concerns arbitrary density operators. The exact copy
counts include integer rounding. The multiplicative asymptotic estimate is
stated for `δ ≤ exp(−1)`; the bound with an additive round holds for all
`0 < δ < 1`, as explained in the manuscript's rounding comment.

The index retains six partially covered and two open background entries.
These are not unproved premises in the numbered results:

| Indexed background | Remaining qualification |
| --- | --- |
| [Gaussian moments](manuscript-index.md#gaussian-moments) | A general first-and-second-moment determination theorem is not exported. |
| [Covariance criteria](manuscript-index.md#covariance-criterion) | Fermionic saturation is checked; the full collection of covariance characterizations is not packaged. |
| [Orthogonal copy symmetries](manuscript-index.md#copy-symmetry) | The full many-copy commutant dualities are not formalized. The copy actions needed by the proofs are checked. |
| [Fermionic second quantization](manuscript-index.md#fermion-second-quantization) | The real rotations used in the proof are checked; the general complex SU(m) description is unused. |
| [Characteristic functions](manuscript-index.md#weyl) | Pure-state injectivity is checked; injectivity for arbitrary mixed states is unused. |
| [Bosonic Gaussian classes](manuscript-index.md#boson-gaussian) | The physical orbit, wavefunction, and characteristic-function identifications used in the proofs are checked. Ground-state and unbounded mean-operator descriptions are unused. |
| [Generator conjugation](manuscript-index.md#boson-invariance) | Kernel, projection, and acceptance invariance are checked. Full unbounded-operator conjugation on domains is not asserted. |
| [Three-copy Fock decomposition](manuscript-index.md#three-copy-fock) | Occupation coordinates implement the argument; an abstract symmetric-Fock direct-sum equivalence is not separately packaged. |

## Proof review

The [comparison report](manuscript-comparison.md#final-review-2026-11-08)
records the statement and proof-strategy review. In particular, the fermionic
span argument includes both parity classes, and the bosonic span argument uses
finite invariant polynomials and Gaussian approximation. The result nodes
record their proof steps; shared preliminaries contain only background used by
the results.

The [whole-library audit](../scripts/NoSorry.lean) rejects `sorry` in every
project declaration, including private helpers, and checks that all library
source files are imported. The [axiom audit](../scripts/Audit.lean) additionally
checks selected public results against
`propext`, `Classical.choice`, and `Quot.sound`. The
[manuscript checks](../scripts/ManuscriptChecks.lean) verify their public types
and selected proof dependencies. All library modules are reachable through
[the public import](../GaussianTesting.lean). Build and maintenance instructions
are in the [development guide](development.md).
