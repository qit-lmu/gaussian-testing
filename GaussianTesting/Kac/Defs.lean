module

/-
Finite-dimensional Lie-algebra model for the bound in Theorem 4.1 (`thm:kac-walk`).

For any (finite-dimensional, unitary) representation of su(2) — given by a Hermitian
angular-momentum triple `Jx, Jy, Jz` with `[Jx,Jy] = i Jz` (cyclic) — the Kac operator

    T = (Πx + Πy + Πz)/3,     Πa = orthogonal projection onto ker Ja,

has `spec(T) ⊆ [0, 7/12] ∪ {1}`, stated as positive semidefiniteness of
`(T - 1)(T - 7/12)`.

Proof: decompose into irreducibles (complete reducibility for su(2); in each
irreducible of spin j the kernels of the three axis generators are at most
one-dimensional, spanned by the zero-weight vectors |0_x⟩, |0_y⟩, |0_z⟩); compute the
pairwise overlaps a_j (zero for odd/half-integer j, `(-1)^{j/2} 2^{-j} C(j, j/2)` for
even j); bound the maximal eigenvalue of the 3×3 Gram matrix by 3·(7/12);
conclude for finite-dimensional triples. `Kac/GeneralRepresentation.lean`
extends this to arbitrary strongly continuous SO(3) representations. The
paper's sharpness witness at j = 4 and the spherical Kac operator remain separate.

Note: no integrality assumption on the representation is needed — half-integer spin
components have no zero-weight vectors, so all three projections vanish there.
-/
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- A Hermitian angular-momentum triple: a unitary representation of su(2) given by
its (Hermitian) generators, `[Jx, Jy] = i Jz` and cyclic permutations thereof. -/
structure AngularMomentum where
  Jx : V →ₗ[ℂ] V
  Jy : V →ₗ[ℂ] V
  Jz : V →ₗ[ℂ] V
  hJx : Jx.IsSymmetric
  hJy : Jy.IsSymmetric
  hJz : Jz.IsSymmetric
  comm_xy : ⁅Jx, Jy⁆ = Complex.I • Jz
  comm_yz : ⁅Jy, Jz⁆ = Complex.I • Jx
  comm_zx : ⁅Jz, Jx⁆ = Complex.I • Jy

variable {V}

/-- The transition operator of the (three-dimensional) Kac walk associated to a
representation: the average of the orthogonal projections onto the kernels of the three
axis generators (eq:def-T). -/
def kacT (J : AngularMomentum V) : V →ₗ[ℂ] V :=
  (3 : ℂ)⁻¹ • (((LinearMap.ker J.Jx).starProjection
      + (LinearMap.ker J.Jy).starProjection
      + (LinearMap.ker J.Jz).starProjection : V →L[ℂ] V) : V →ₗ[ℂ] V)

end

end GaussianTesting
