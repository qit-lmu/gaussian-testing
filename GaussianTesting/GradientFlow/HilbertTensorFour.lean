module

public import GaussianTesting.GradientFlow.HilbertTensor

@[expose] public section

/-!
# Four completed Hilbert tensor factors

The four-copy bosonic measurement groups copies 1 and 3 separately from copies
2 and 4. The unitary `hilbertReshuffle` implements this regrouping on completed
Hilbert tensor products, without choosing bases.
-/

namespace GaussianTesting

open scoped TensorProduct InnerProductSpace
open UniformSpace

noncomputable section

variable {E F G K : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Tensoring two unitary equivalences gives a unitary on the completed tensor
products. -/
def hilbertTensorEquiv (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] K) :
    HilbertTensor E F ≃ₗᵢ[ℂ] HilbertTensor G K := by
  let L := (TensorProduct.congrIsometry e f).toLinearIsometry.completion
  let R := (TensorProduct.congrIsometry e.symm f.symm).toLinearIsometry.completion
  refine LinearIsometryEquiv.ofSurjective L fun z => ⟨R z, ?_⟩
  refine Completion.induction_on z
    (isClosed_eq (L.continuous.comp R.continuous) continuous_id) fun w => ?_
  simp [L, R, LinearIsometry.completion_apply_coe, ← TensorProduct.congrIsometry_symm]

@[simp] theorem hilbertTensorEquiv_tmul (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] K)
    (x : E) (y : F) :
    hilbertTensorEquiv e f (hilbertTmul x y) = hilbertTmul (e x) (f y) := by
  exact (TensorProduct.congrIsometry e f).toLinearIsometry.completion_apply_coe
    (x ⊗ₜ[ℂ] y)

theorem hilbertTensorEquiv_toContinuousLinearMap
    (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] K) :
    (hilbertTensorEquiv e f).toLinearIsometry.toContinuousLinearMap =
      hilbertTensorMap e.toLinearIsometry.toContinuousLinearMap
        f.toLinearIsometry.toContinuousLinearMap := by
  apply hilbertTensor_ext
  intro x y
  simp

@[simp] theorem hilbertTensorEquiv_symm (e : E ≃ₗᵢ[ℂ] G) (f : F ≃ₗᵢ[ℂ] K) :
    (hilbertTensorEquiv e f).symm = hilbertTensorEquiv e.symm f.symm := by
  have h : (hilbertTensorEquiv e f).toLinearIsometry.toContinuousLinearMap.comp
      (hilbertTensorEquiv e.symm f.symm).toLinearIsometry.toContinuousLinearMap =
        ContinuousLinearMap.id ℂ _ := by
    apply hilbertTensor_ext
    intro x y
    simp
  ext v
  apply (hilbertTensorEquiv e f).injective
  simpa using (DFunLike.congr_fun h v).symm

@[simp] theorem hilbertAssoc_symm_tmul (x : E) (y : F) (z : G) :
    hilbertAssoc.symm (hilbertTmul x (hilbertTmul y z)) =
      hilbertTmul (hilbertTmul x y) z := by
  apply hilbertAssoc.injective
  simp

/-- Regroup four completed factors from `(12)(34)` to `(13)(24)`. This is the
copy permutation used to apply the bosonic accepting projection to copies 2
and 4 in the manuscript's four-copy measurement. -/
def hilbertReshuffle :
    HilbertTensor (HilbertTensor E F) (HilbertTensor G K) ≃ₗᵢ[ℂ]
      HilbertTensor (HilbertTensor E G) (HilbertTensor F K) :=
  (hilbertAssoc (E := E) (F := F) (G := HilbertTensor G K)).trans
    ((hilbertTensorEquiv (LinearIsometryEquiv.refl ℂ E)
      ((hilbertAssoc (E := F) (F := G) (G := K)).symm.trans
        ((hilbertTensorEquiv (hilbertSwap (E := F) (F := G))
          (LinearIsometryEquiv.refl ℂ K)).trans hilbertAssoc))).trans
      (hilbertAssoc (E := E) (F := G) (G := HilbertTensor F K)).symm)

@[simp] theorem hilbertReshuffle_tmul (x : E) (y : F) (z : G) (w : K) :
    hilbertReshuffle (hilbertTmul (hilbertTmul x y) (hilbertTmul z w)) =
      hilbertTmul (hilbertTmul x z) (hilbertTmul y w) := by
  simp [hilbertReshuffle]

/-- Continuous linear maps out of four completed factors are determined by
their values on elementary four-factor tensors. -/
theorem hilbertTensorFour_ext {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f g : HilbertTensor (HilbertTensor E F) (HilbertTensor G K) →L[ℂ] H}
    (h : ∀ x y z w,
      f (hilbertTmul (hilbertTmul x y) (hilbertTmul z w)) =
        g (hilbertTmul (hilbertTmul x y) (hilbertTmul z w))) : f = g := by
  apply hilbertTensor_ext
  intro u v
  refine hilbertTensor_induction (p := fun a => f (hilbertTmul a v) = g (hilbertTmul a v))
    (isClosed_eq (f.continuous.comp (hilbertTmul.flip v).continuous)
      (g.continuous.comp (hilbertTmul.flip v).continuous)) ?_ ?_ u
  · intro x y
    refine hilbertTensor_induction
      (p := fun b => f (hilbertTmul (hilbertTmul x y) b) =
        g (hilbertTmul (hilbertTmul x y) b))
      (isClosed_eq (f.continuous.comp (hilbertTmul (hilbertTmul x y)).continuous)
        (g.continuous.comp (hilbertTmul (hilbertTmul x y)).continuous))
      (h x y) ?_ v
    intro a b ha hb
    simp only [map_add, ha, hb]
  · intro a b ha hb
    simp only [map_add, add_apply, ha, hb]

/-- The inverse regrouping is the same permutation of the middle factors. -/
@[simp] theorem hilbertReshuffle_symm :
    (hilbertReshuffle (E := E) (F := F) (G := G) (K := K)).symm =
      hilbertReshuffle (E := E) (F := G) (G := F) (K := K) := by
  have h :
      (hilbertReshuffle (E := E) (F := F) (G := G) (K := K)).toLinearIsometry.toContinuousLinearMap.comp
        (hilbertReshuffle (E := E) (F := G) (G := F) (K := K)).toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ := by
    apply hilbertTensorFour_ext
    intro x y z w
    simp
  ext v
  apply (hilbertReshuffle (E := E) (F := F) (G := G) (K := K)).injective
  simpa using (DFunLike.congr_fun h v).symm

/-- Swapping the middle copies twice restores the original four-copy vector. -/
@[simp] theorem hilbertReshuffle_involution
    (v : HilbertTensor (HilbertTensor E F) (HilbertTensor G K)) :
    hilbertReshuffle (hilbertReshuffle v) = v := by
  rw [← hilbertReshuffle_symm]
  exact LinearIsometryEquiv.symm_apply_apply _ _

end

end GaussianTesting
