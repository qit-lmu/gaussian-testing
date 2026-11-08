module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.GradientFlow.HilbertTensor

@[expose] public section

/-!
# Rank-one projections on completed tensor products

Tensoring by a rank-one projection is the composition of contraction against
its range vector and tensoring with that vector. These generic Hilbert-space
facts support partial-trace factorization and projection-based tests.
-/

namespace GaussianTesting

open scoped InnerProductSpace TensorProduct

noncomputable section

/-- Tensoring with a rank-one operator factors through tensoring with its
range vector and the adjoint contraction. -/
theorem hilbertTensorMap_rankOne_right {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (v : F) :
    hilbertTensorMap (ContinuousLinearMap.id ℂ E) (InnerProductSpace.rankOne ℂ v v) =
      (hilbertTmul.flip v).comp (hilbertTmul.flip v).adjoint := by
  let J : E →L[ℂ] HilbertTensor E F := hilbertTmul.flip v
  have hj (x : E) (y : F) : J.adjoint (hilbertTmul x y) = inner ℂ v y • x := by
    apply ext_inner_left ℂ
    intro z
    rw [J.adjoint_inner_right]
    change inner ℂ (hilbertTmul z v) (hilbertTmul x y) = inner ℂ z (inner ℂ v y • x)
    rw [inner_hilbertTmul, inner_smul_right, mul_comm]
  apply hilbertTensor_ext
  intro x y
  rw [hilbertTensorMap_tmul, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  change hilbertTmul x (InnerProductSpace.rankOne ℂ v v y) = J (J.adjoint (hilbertTmul x y))
  rw [hj, map_smul]
  simp only [InnerProductSpace.rankOne_apply, map_smul]
  rfl

/-- A unit vector has unit expectation in an orthogonal projection exactly when it is fixed. -/
theorem projection_expectation_one_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (P : E →L[ℂ] E)
    (hs : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hi : ∀ x, P (P x) = P x) (v : E) (hv : ‖v‖ = 1) :
    (inner ℂ v (P v)).re = 1 ↔ P v = v := by
  have hp : inner ℂ (P v) (P v) = inner ℂ v (P v) :=
    (hs v (P v)).trans (congrArg (inner ℂ v) (hi v))
  have hp' : ‖P v‖^2 = (inner ℂ v (P v)).re :=
    (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans (congrArg Complex.re hp)
  constructor
  · intro h
    have hz : ‖v - P v‖^2 = 0 := by
      rw [@norm_sub_sq ℂ, hv, hp', h]
      change (1 : ℝ)^2 - 2 * (inner ℂ v (P v)).re + 1 = 0
      rw [h]
      norm_num
    exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
  · intro h
    rw [h, inner_self_eq_norm_sq_to_K, hv]
    norm_num


/-- A fixed vector of a rank-one projection on the second factor has that
vector as a tensor factor. -/
theorem exists_factor_of_tensor_rankOne_fixed {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (v : F) (w : HilbertTensor E F)
    (hw : hilbertTensorMap (ContinuousLinearMap.id ℂ E)
      (InnerProductSpace.rankOne ℂ v v) w = w) :
    ∃ u : E, w = hilbertTmul u v := by
  rw [hilbertTensorMap_rankOne_right] at hw
  exact ⟨(hilbertTmul.flip v).adjoint w, hw.symm⟩

/-- The norm of an elementary tensor in the Hilbert completion. -/
theorem norm_hilbertTmul {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x : E) (y : F) :
    ‖hilbertTmul x y‖ = ‖x‖ * ‖y‖ := by
  change ‖(↑(x ⊗ₜ[ℂ] y) : HilbertTensor E F)‖ = _
  rw [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

end
end GaussianTesting
