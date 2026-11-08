module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PartialTrace
public import GaussianTesting.GradientFlow.RankOneTensor

@[expose] public section

/-!
# Pure reduced states give product vectors

For a bipartite unit vector, a rank-one right reduced density operator means
that the right rank-one projection has expectation one. The projection fixes
the vector, and its explicit tensor contraction gives the product factor.
This is the purity prerequisite used by the Gaussian bosonic test.
-/

namespace GaussianTesting.HilbertDensity

open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ : Type*}

/-- A bipartite unit vector whose right reduced state is the projector onto
`φ` is a product with right factor `φ`. The first factor is also a unit vector. -/
theorem exists_unit_tmul_of_reducedRight_eq_rankOne
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (Φ : HilbertTensor E F) (hΦ : ‖Φ‖ = 1) (φ : F) (hφ : ‖φ‖ = 1)
    (hρ : reducedRight b c Φ = InnerProductSpace.rankOne ℂ φ φ) :
    ∃ u : E, ‖u‖ = 1 ∧ Φ = hilbertTmul u φ := by
  let J : E →L[ℂ] HilbertTensor E F := hilbertTmul.flip φ
  let P := hilbertTensorMap (ContinuousLinearMap.id ℂ E) (InnerProductSpace.rankOne ℂ φ φ)
  have hs (x y : HilbertTensor E F) : inner ℂ (P x) y = inner ℂ x (P y) := by
    change inner ℂ ((hilbertTensorMap _ _) x) y = inner ℂ x ((hilbertTensorMap _ _) y)
    rw [hilbertTensorMap_rankOne_right]
    change inner ℂ (J (J.adjoint x)) y = inner ℂ x (J (J.adjoint y))
    rw [← J.adjoint_inner_right, J.adjoint_inner_left]
  have hi (x : HilbertTensor E F) : P (P x) = P x := by
    have hh : P.comp P = P := by
      apply hilbertTensor_ext
      intro u v
      simp only [P, ContinuousLinearMap.comp_apply, hilbertTensorMap_tmul,
        ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hφ, RCLike.ofReal_one, one_pow, mul_one]
    exact congrArg (fun A => A x) hh
  have he : (inner ℂ Φ (P Φ)).re = 1 := by
    have h := operatorTrace_mul_reducedRight b c Φ (InnerProductSpace.rankOne ℂ φ φ)
    rw [hρ, operatorTrace_rankOne_mul] at h
    have hleft : inner ℂ φ ((InnerProductSpace.rankOne ℂ φ φ) φ) = 1 := by
      simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hφ]
    rw [hleft] at h
    exact congrArg Complex.re h.symm
  have hfix : P Φ = Φ := (projection_expectation_one_iff P hs hi Φ hΦ).mp he
  obtain ⟨u, hu⟩ := exists_factor_of_tensor_rankOne_fixed φ Φ hfix
  refine ⟨u, ?_, hu⟩
  have hn := congrArg norm hu
  simpa only [hΦ, norm_hilbertTmul, hφ, mul_one] using hn.symm

end
end GaussianTesting.HilbertDensity
