module

/-
Finite-dimensional Lie-algebra bound related to Theorem 4.1 (`thm:kac-walk`),
interface file. The arbitrary-representation extension is proved in
`Kac/GeneralRepresentation.lean`; the exact gap of the spherical Kac walk
remains separate from this polynomial inequality.

The definitions (`AngularMomentum`, `kacT`) live in `Kac/Defs.lean`; the proof is in
`Kac/Gap.lean` (reduction to irreducibles by orthocomplement induction + the
string-basis/tridiagonal-kernel/Gram computation on irreducibles) with the binomial
inputs in `Kac/Binomial.lean`.
-/
public import GaussianTesting.Kac.Gap

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- **Theorem 4.1, finite Lie-algebra bound** (thm:kac-walk): positive
semidefiniteness of `(T - I)(T - (7/12)I)`. -/
theorem kacT_gap (J : AngularMomentum V) (f : V) :
    0 ≤ (⟪f, ((kacT J - LinearMap.id) ∘ₗ
        (kacT J - (((7 / 12 : ℝ) : ℂ) • LinearMap.id))) f⟫_ℂ).re :=
  J.kacGapOn_all f

end

end GaussianTesting
