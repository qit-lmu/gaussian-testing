module

public import GaussianTesting.GradientFlow.LocalFlow

@[expose] public section

/-! # The unit-sphere field and the phase of a representative

The field of Eq. (3.4) is horizontal and transforms equivariantly under
unit scalars. In particular, the local solution changes by the same constant
phase when its initial representative is changed.
-/

namespace GaussianTesting.TensorSquare

open scoped InnerProductSpace ComplexConjugate
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (T : TensorSquare H K) (P : K →L[ℂ] K)

private lemma conj_mul_eq_one {z : ℂ} (hz : ‖z‖ = 1) : conj z * z = 1 := by
  rw [Complex.conj_mul', hz]; norm_num

omit [CompleteSpace H] [CompleteSpace K] in
/-- A global phase leaves the acceptance probability unchanged. -/
theorem accProbA_phase (z : ℂ) (hz : ‖z‖ = 1) (x : H) :
    T.accProbA P (z • x) = T.accProbA P x := by
  have h := conj_mul_eq_one hz
  unfold accProbA
  simp only [map_smul, smul_apply, inner_smul_left, inner_smul_right]
  congr 1
  calc
    _ = (conj z * z) * (conj z * z) * ⟪T.tp x x, P (T.tp x x)⟫_ℂ := by ring
    _ = _ := by rw [h]; ring

/-- The gradient field of Eq. (3.4) commutes with changes of phase. -/
theorem gradAccA_phase (z : ℂ) (hz : ‖z‖ = 1) (x : H) :
    T.gradAccA P (z • x) = z • T.gradAccA P x := by
  have hK : T.KvecA P (z • x) = z • T.KvecA P x := by
    apply ext_inner_left ℂ
    intro w
    simp only [KvecA, T.inner_contr, map_smul, smul_apply,
      inner_smul_left, inner_smul_right]
    calc
      _ = (conj z * z) * (z * ⟪T.tp w x, P (T.tp x x)⟫_ℂ) := by ring
      _ = _ := by rw [conj_mul_eq_one hz, one_mul]
  rw [gradAccA, T.accProbA_phase P z hz, hK, gradAccA]
  simp only [smul_sub, smul_comm z (4 : ℂ), smul_comm z ((T.accProbA P x : ℝ) : ℂ)]

/-- On the unit sphere the gradient is complex-orthogonal to the current
representative, so its velocity is horizontal for the projection to rays. -/
theorem inner_gradAccA_eq_zero {P : K →L[ℂ] K} (hP : T.IsAcceptance P) {x : H}
    (hx : ‖x‖ = 1) : ⟪x, T.gradAccA P x⟫_ℂ = 0 := by
  rw [gradAccA, inner_smul_right, inner_sub_right, inner_smul_right, T.inner_psi_KvecA,
    T.inner_tp_P_self hP, inner_self_eq_norm_sq_to_K, hx]
  norm_num

/-- Changing the initial phase of a solution changes its entire unit lift by that phase. -/
theorem IsUnitFlowOn.phase {T : TensorSquare H K} {P : K →L[ℂ] K} {γ : ℝ → H} {s : Set ℝ}
    (hγ : T.IsUnitFlowOn P γ s) {z : ℂ} (hz : ‖z‖ = 1) :
    T.IsUnitFlowOn P (fun t => z • γ t) s := by
  constructor
  · intro t ht
    rw [norm_smul, hz, hγ.sphere t ht, mul_one]
  · intro t ht
    rw [T.gradAccA_phase P z hz]
    exact (hγ.deriv t ht).const_smul z

end GaussianTesting.TensorSquare
