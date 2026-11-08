module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Kac.Defs
public import GaussianTesting.Kac.SO3OneParameter

@[expose] public section

/-!
# From skew-adjoint generators to angular momentum

The generators `Dₐ` of the unitary axis actions satisfy `[Dₓ,Dᵧ] = D_z`.
The manuscript's Hermitian generators are `Jₐ = i Dₐ`, so that their
commutator relation is `[Jₓ,Jᵧ] = i J_z`. Their kernels coincide.
-/

namespace GaussianTesting

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem imaginary_smul_commutator
    (D B C : E →L[ℂ] E) (hcomm : D * B - B * D = C) :
    ⁅Complex.I • D.toLinearMap, Complex.I • B.toLinearMap⁆ =
      Complex.I • (Complex.I • C.toLinearMap) := by
  have h : D.toLinearMap * B.toLinearMap - B.toLinearMap * D.toLinearMap =
      C.toLinearMap := congrArg ContinuousLinearMap.toLinearMap hcomm
  rw [Ring.lie_def, smul_mul_smul_comm, smul_mul_smul_comm, smul_smul,
    Complex.I_mul_I]
  simp only [neg_one_smul]
  calc
    _ = -(D.toLinearMap * B.toLinearMap - B.toLinearMap * D.toLinearMap) := by abel
    _ = _ := congrArg Neg.neg h

/-- Convert the skew-adjoint infinitesimal generators of the three rotations
into the Hermitian triple used by the finite-dimensional Kac bound. -/
def angularMomentumOfSkewGenerators [FiniteDimensional ℂ E]
    (Dx Dy Dz : E →L[ℂ] E)
    (hx : ∀ v w, inner ℂ (Dx v) w = -inner ℂ v (Dx w))
    (hy : ∀ v w, inner ℂ (Dy v) w = -inner ℂ v (Dy w))
    (hz : ∀ v w, inner ℂ (Dz v) w = -inner ℂ v (Dz w))
    (hxy : Dx * Dy - Dy * Dx = Dz)
    (hyz : Dy * Dz - Dz * Dy = Dx)
    (hzx : Dz * Dx - Dx * Dz = Dy) : AngularMomentum E where
  Jx := Complex.I • Dx.toLinearMap
  Jy := Complex.I • Dy.toLinearMap
  Jz := Complex.I • Dz.toLinearMap
  hJx := imaginary_smul_generator_isSymmetric Dx hx
  hJy := imaginary_smul_generator_isSymmetric Dy hy
  hJz := imaginary_smul_generator_isSymmetric Dz hz
  comm_xy := by exact imaginary_smul_commutator Dx Dy Dz hxy
  comm_yz := by exact imaginary_smul_commutator Dy Dz Dx hyz
  comm_zx := by exact imaginary_smul_commutator Dz Dx Dy hzx

/-- Multiplying an infinitesimal generator by `i` preserves its kernel. -/
theorem imaginary_smul_generator_ker (D : E →L[ℂ] E) :
    LinearMap.ker (Complex.I • D.toLinearMap) = LinearMap.ker D.toLinearMap := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.smul_apply, smul_eq_zero, Complex.I_ne_zero,
    false_or]

end
end GaussianTesting
