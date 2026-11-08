module

public import GaussianTesting.GradientFlow.Abstract
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

/-!
# The contracted acceptance operator

The unnumbered claim after Lemma 3.1 defines
`K_ψ = (I ⊗ ⟨ψ|) P (I ⊗ |ψ⟩)`.  Here the insertion `x ↦ x ⊗ ψ`
and its Hilbert adjoint realize this operator on any complete complex Hilbert
space. Its value on `ψ` is the vector already used in the gradient and moment
formulas. Positivity and contractivity follow by compressing the acceptance
projection, and Eq. (3.4) gives the critical-point characterization.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace H] [CompleteSpace K]

namespace TensorSquare

variable (T : TensorSquare H K) (P : K →L[ℂ] K)

/-- The manuscript's operator `K_ψ`, the compression of `P` by `x ↦ x ⊗ ψ`. -/
def contractionOperator (ψ : H) : H →L[ℂ] H :=
  (T.tp.flip ψ).adjoint ∘L P ∘L (T.tp.flip ψ)

/-- The operator is precisely contraction with the second copy after applying `P`. -/
theorem contractionOperator_apply (ψ x : H) :
    T.contractionOperator P ψ x = T.contr ψ (P (T.tp x ψ)) := by
  apply ext_inner_left ℂ
  intro v
  simp only [contractionOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.flip_apply,
    T.inner_contr]

/-- The previously defined contracted vector is the value of `K_ψ` on `ψ`. -/
@[simp] theorem contractionOperator_self (ψ : H) :
    T.contractionOperator P ψ ψ = T.KvecA P ψ :=
  T.contractionOperator_apply P ψ ψ

variable {P}

/-- Compression preserves positivity of the orthogonal acceptance projection. -/
theorem contractionOperator_isPositive (hP : T.IsAcceptance P) (ψ : H) :
    (T.contractionOperator P ψ).IsPositive := by
  have hpos : P.IsPositive := .of_isStarProjection
    ⟨hP.idem, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hP.symmetric⟩
  exact hpos.adjoint_conj (T.tp.flip ψ)

/-- In particular, the manuscript's contracted operator is self-adjoint. -/
theorem contractionOperator_isSelfAdjoint (hP : T.IsAcceptance P) (ψ : H) :
    IsSelfAdjoint (T.contractionOperator P ψ) :=
  (T.contractionOperator_isPositive hP ψ).isSelfAdjoint

/-- For a unit second copy, `K_ψ` is a contraction in operator norm. -/
theorem norm_contractionOperator_le_one (hP : T.IsAcceptance P) {ψ : H}
    (hψ : ‖ψ‖ = 1) : ‖T.contractionOperator P ψ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [T.contractionOperator_apply]
  calc
    ‖T.contr ψ (P (T.tp x ψ))‖ ≤ ‖ψ‖ * ‖P (T.tp x ψ)‖ := T.norm_contr_le _ _
    _ ≤ ‖ψ‖ * (‖P‖ * ‖T.tp x ψ‖) :=
      mul_le_mul_of_nonneg_left (P.le_opNorm _) (norm_nonneg ψ)
    _ ≤ ‖ψ‖ * (1 * ‖T.tp x ψ‖) := by gcongr; exact hP.norm_le_one
    _ = 1 * ‖x‖ := by rw [T.norm_tp, hψ]; ring

/-- The first moment of `K_ψ` is exactly the real acceptance probability. -/
theorem contractionOperator_first_moment (hP : T.IsAcceptance P) (ψ : H) :
    ⟪ψ, T.contractionOperator P ψ ψ⟫_ℂ = (T.accProbA P ψ : ℂ) := by
  rw [T.contractionOperator_self, T.inner_psi_KvecA, T.inner_tp_P_self hP]

/-- The second moment of `K_ψ` is the quantity `q` in Eq. (3.5). -/
theorem contractionOperator_second_moment (hP : T.IsAcceptance P) (ψ : H) :
    ⟪ψ, (T.contractionOperator P ψ ^ 2) ψ⟫_ℂ = (T.qProbA P ψ : ℂ) := by
  rw [pow_two, mul_apply_eq_comp,
    ← (T.contractionOperator_isPositive hP ψ).inner_left_eq_inner_right]
  simp [T.contractionOperator_self, qProbA, inner_self_eq_norm_sq_to_K]

/-- Eq. (3.4), expressed with the manuscript's operator `K_ψ`. -/
theorem gradAccA_eq_contractionOperator (ψ : H) :
    T.gradAccA P ψ = (4 : ℂ) •
      (T.contractionOperator P ψ ψ - (T.accProbA P ψ : ℂ) • ψ) := by
  rw [T.contractionOperator_self]
  rfl

/-- The variance interpretation of Eq. (3.5) for the actual operator `K_ψ`. -/
theorem norm_gradAccA_sq_eq_variance (hP : T.IsAcceptance P) {ψ : H}
    (hψ : ‖ψ‖ = 1) :
    ‖T.gradAccA P ψ‖ ^ 2 = 16 *
      ((⟪ψ, (T.contractionOperator P ψ ^ 2) ψ⟫_ℂ).re -
        (⟪ψ, T.contractionOperator P ψ ψ⟫_ℂ).re ^ 2) := by
  rw [T.contractionOperator_first_moment hP, T.contractionOperator_second_moment hP]
  exact T.norm_gradAccA_sq hP hψ

/-- The acceptance gradient vanishes exactly at the manuscript's eigenvector equation. -/
theorem gradAccA_eq_zero_iff_contractionOperator (ψ : H) :
    T.gradAccA P ψ = 0 ↔
      T.contractionOperator P ψ ψ = (T.accProbA P ψ : ℂ) • ψ := by
  rw [T.gradAccA_eq_contractionOperator]
  simp only [smul_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero]

end TensorSquare

end

end GaussianTesting
