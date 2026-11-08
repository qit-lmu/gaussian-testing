module

public import GaussianTesting.Bosons.Mixed
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-!
# Completed Hilbert tensor products

The square and cube in Section 3 are Hilbert completions of algebraic tensor
products for the inner product on elementary tensors. The coordinate maps
identify these completions with the corresponding product-indexed ℓ² spaces.
-/
namespace GaussianTesting

open scoped TensorProduct InnerProductSpace
open UniformSpace Set

noncomputable section

/-- The completion in the Hilbert tensor norm. -/
abbrev HilbertTensor (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] := Completion (E ⊗[ℂ] F)

/-- The completed two-copy Hilbert space. -/
abbrev HilbertSquare (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  HilbertTensor E E

/-- Three copies, grouped as the first factor and the completed last two. -/
abbrev HilbertCube (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  HilbertTensor E (HilbertSquare E)

variable {E F G K : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The continuous bilinear elementary tensor in the completion. -/
def hilbertTmul : E →L[ℂ] F →L[ℂ] HilbertTensor E F :=
  (ContinuousLinearMap.compL ℂ F (E ⊗[ℂ] F) (HilbertTensor E F)
    Completion.toComplL).comp (TensorProduct.mkL ℂ E F)

@[simp] theorem inner_hilbertTmul (x x' : E) (y y' : F) :
    ⟪hilbertTmul x y, hilbertTmul x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  exact (Completion.inner_coe (𝕜 := ℂ) (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y')).trans
    (TensorProduct.inner_tmul ℂ x x' y y')

/-- A bounded operator on each factor acts on their completed tensor product. -/
def hilbertTensorMap (f : E →L[ℂ] G) (g : F →L[ℂ] K) :
    HilbertTensor E F →L[ℂ] HilbertTensor G K := (TensorProduct.mapL f g).completion

@[simp] theorem hilbertTensorMap_tmul (f : E →L[ℂ] G) (g : F →L[ℂ] K) (x : E) (y : F) :
    hilbertTensorMap f g (hilbertTmul x y) = hilbertTmul (f x) (g y) := by
  exact (TensorProduct.mapL f g).completion_apply_coe (x ⊗ₜ[ℂ] y)

/-- Closed additive properties of vectors in a completed tensor product are
determined by elementary tensors. -/
theorem hilbertTensor_induction {p : HilbertTensor E F → Prop}
    (hclosed : IsClosed {z | p z}) (hpure : ∀ x y, p (hilbertTmul x y))
    (hadd : ∀ u v, p u → p v → p (u + v)) (z : HilbertTensor E F) : p z := by
  refine Completion.induction_on z hclosed fun w => ?_
  induction w using TensorProduct.inductionOn with
  | tmul x y => exact hpure x y
  | add u v hu hv =>
    rw [Completion.coe_add]
    exact hadd _ _ hu hv

/-- Continuous linear maps out of the completion agree if they agree on all pure tensors. -/
theorem hilbertTensor_ext {f g : HilbertTensor E F →L[ℂ] G}
    (h : ∀ x y, f (hilbertTmul x y) = g (hilbertTmul x y)) : f = g := by
  ext z
  apply hilbertTensor_induction (p := fun w => f w = g w) (isClosed_eq f.continuous g.continuous) h
  intro u v hu hv
  simp only [map_add, hu, hv]

@[simp] theorem hilbertTensorMap_id :
    hilbertTensorMap (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ F) =
      ContinuousLinearMap.id ℂ (HilbertTensor E F) := by
  apply hilbertTensor_ext
  intro x y
  simp

theorem hilbertTensorMap_comp {G' K' : Type*}
    [NormedAddCommGroup G'] [InnerProductSpace ℂ G']
    [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    (f : E →L[ℂ] G) (g : F →L[ℂ] K) (u : G →L[ℂ] G') (v : K →L[ℂ] K') :
    hilbertTensorMap (u.comp f) (v.comp g) = (hilbertTensorMap u v).comp (hilbertTensorMap f g) := by
  apply hilbertTensor_ext
  intro x y
  simp

/-- The linear span of the elementary tensors is dense. -/
theorem dense_span_hilbertTmul :
    Dense (Submodule.span ℂ (Set.range fun p : E × F => hilbertTmul p.1 p.2) :
      Set (HilbertTensor E F)) := by
  let U := Submodule.span ℂ (Set.range fun p : E × F => hilbertTmul p.1 p.2)
  intro z
  change z ∈ U.topologicalClosure
  apply hilbertTensor_induction (p := fun w => w ∈ U.topologicalClosure)
    U.isClosed_topologicalClosure
  · intro x y
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(x,y), rfl⟩)
  · exact fun _ _ => U.topologicalClosure.add_mem

/-- Three elementary factors have dense linear span in the completed cube. -/
theorem dense_span_hilbertTriple :
    Dense (Submodule.span ℂ (Set.range fun p : E × E × E =>
      hilbertTmul p.1 (hilbertTmul p.2.1 p.2.2)) : Set (HilbertCube E)) := by
  let U := Submodule.span ℂ (Set.range fun p : E × E × E =>
    hilbertTmul p.1 (hilbertTmul p.2.1 p.2.2))
  intro z
  change z ∈ U.topologicalClosure
  apply hilbertTensor_induction (p := fun w => w ∈ U.topologicalClosure)
    U.isClosed_topologicalClosure
  · intro x w
    refine hilbertTensor_induction (p := fun v => hilbertTmul x v ∈ U.topologicalClosure)
      (U.isClosed_topologicalClosure.preimage (hilbertTmul x).continuous) ?_ ?_ w
    · intro y z
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(x, y, z), rfl⟩)
    · intro a b ha hb
      rw [map_add]
      exact U.topologicalClosure.add_mem ha hb
  · exact fun _ _ => U.topologicalClosure.add_mem

def completeIsometryEquiv (e : E ≃ₗᵢ[ℂ] F) : Completion E ≃ₗᵢ[ℂ] Completion F := by
  let L := e.toLinearIsometry.completion
  refine LinearIsometryEquiv.ofSurjective L fun v => ?_
  use e.symm.toLinearIsometry.completion v
  refine Completion.induction_on v
    (isClosed_eq (L.continuous.comp e.symm.toLinearIsometry.completion.continuous) continuous_id)
    fun w => ?_
  simp [L, LinearIsometry.completion_apply_coe]

/-- Swapping the factors extends the algebraic swap to a unitary on the completion. -/
def hilbertSwap : HilbertTensor E F ≃ₗᵢ[ℂ] HilbertTensor F E :=
  completeIsometryEquiv (TensorProduct.commIsometry ℂ E F)

@[simp] theorem hilbertSwap_tmul (x : E) (y : F) :
    hilbertSwap (hilbertTmul x y) = hilbertTmul y x := by
  exact (TensorProduct.commIsometry ℂ E F).toLinearIsometry.completion_apply_coe (x ⊗ₜ[ℂ] y)

/-- The abstract two-copy interface on the completed Hilbert tensor square. -/
def hilbertTensorSquare (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    TensorSquare E (HilbertSquare E) where
  tp := hilbertTmul
  inner_tp := fun x y u v => inner_hilbertTmul x u y v
  swap := hilbertSwap (E := E) (F := E)
  swap_tp := fun x y => hilbertSwap_tmul x y

def tensorOfDenseIsometries (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] K)
    (hf : DenseRange f) (hg : DenseRange g) :
    HilbertTensor E F ≃ₗᵢ[ℂ] HilbertTensor G K := by
  let L := (TensorProduct.mapIsometry f g).completion
  let U := L.toLinearMap.range
  have hc : IsClosed (U : Set (HilbertTensor G K)) := L.isometry.isClosedEmbedding.isClosed_range
  refine LinearIsometryEquiv.ofSurjective L fun z => ?_
  change z ∈ U
  apply hilbertTensor_induction hc
  · intro x y
    apply isClosed_property (hf.prodMap hg)
      (p := fun p : G × K => hilbertTmul p.1 p.2 ∈ U)
      (hc.preimage hilbertTmul.continuous₂) _ (x, y)
    rintro ⟨x, y⟩
    exact ⟨hilbertTmul x y, (TensorProduct.mapIsometry f g).completion_apply_coe (x ⊗ₜ[ℂ] y)⟩
  · exact fun _ _ => U.add_mem

private theorem tensorOfDenseIsometries_tmul (f : E →ₗᵢ[ℂ] G) (g : F →ₗᵢ[ℂ] K)
    (hf : DenseRange f) (hg : DenseRange g) (x : E) (y : F) :
    tensorOfDenseIsometries f g hf hg (hilbertTmul x y) = hilbertTmul (f x) (g y) :=
  (TensorProduct.mapIsometry f g).completion_apply_coe (x ⊗ₜ[ℂ] y)

def tensorCompleteLeft :
    HilbertTensor (E ⊗[ℂ] F) G ≃ₗᵢ[ℂ] HilbertTensor (HilbertTensor E F) G :=
  tensorOfDenseIsometries Completion.toComplₗᵢ (.id : G →ₗᵢ[ℂ] G)
    Completion.denseRange_coe denseRange_id

def tensorCompleteRight :
    HilbertTensor E (F ⊗[ℂ] G) ≃ₗᵢ[ℂ] HilbertTensor E (HilbertTensor F G) :=
  tensorOfDenseIsometries (.id : E →ₗᵢ[ℂ] E) Completion.toComplₗᵢ
    denseRange_id Completion.denseRange_coe

/-- Reassociate three completed Hilbert tensor factors. -/
def hilbertAssoc :
    HilbertTensor (HilbertTensor E F) G ≃ₗᵢ[ℂ] HilbertTensor E (HilbertTensor F G) :=
  (tensorCompleteLeft (E := E) (F := F) (G := G)).symm.trans
    ((completeIsometryEquiv (TensorProduct.assocIsometry ℂ E F G)).trans tensorCompleteRight)

@[simp] theorem hilbertAssoc_tmul (x : E) (y : F) (z : G) :
    hilbertAssoc (hilbertTmul (hilbertTmul x y) z) = hilbertTmul x (hilbertTmul y z) := by
  have hleft : tensorCompleteLeft (hilbertTmul (x ⊗ₜ[ℂ] y) z) = hilbertTmul (hilbertTmul x y) z :=
    tensorOfDenseIsometries_tmul _ _ _ _ _ _
  have hassoc : completeIsometryEquiv (TensorProduct.assocIsometry ℂ E F G)
      (hilbertTmul (x ⊗ₜ[ℂ] y) z) = hilbertTmul x (y ⊗ₜ[ℂ] z) :=
    (TensorProduct.assocIsometry ℂ E F G).toLinearIsometry.completion_apply_coe
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)
  rw [hilbertAssoc, LinearIsometryEquiv.trans_apply, ← hleft,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.trans_apply, hassoc]
  exact tensorOfDenseIsometries_tmul _ _ _ _ _ _

variable {ι κ : Type*}

/-- Product coordinates on the algebraic tensor product. -/
def coordinateMap (e : E ≃ₗᵢ[ℂ] L2 ι) (f : F ≃ₗᵢ[ℂ] L2 κ) :
    E ⊗[ℂ] F →ₗ[ℂ] L2 (ι × κ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun x y => tpPair (e x) (f y))
    (by
      intro a b y
      apply lp.ext; funext i
      simp [add_mul])
    (by
      intro c x y
      apply lp.ext; funext i
      simp [mul_assoc])
    (by
      intro x a b
      apply lp.ext; funext i
      simp [mul_add])
    (by
      intro c x y
      apply lp.ext; funext i
      simp [mul_left_comm]))

private theorem coordinateMap_tmul (e : E ≃ₗᵢ[ℂ] L2 ι) (f : F ≃ₗᵢ[ℂ] L2 κ) (x : E) (y : F) :
    coordinateMap e f (x ⊗ₜ[ℂ] y) = tpPair (e x) (f y) := rfl

def coordinateIsometry (e : E ≃ₗᵢ[ℂ] L2 ι) (f : F ≃ₗᵢ[ℂ] L2 κ) :
    E ⊗[ℂ] F →ₗᵢ[ℂ] L2 (ι × κ) :=
  (coordinateMap e f).isometryOfInner fun u v => by
    induction u using TensorProduct.inductionOn with
    | tmul x y =>
      induction v using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [coordinateMap_tmul, inner_tpPair, LinearIsometryEquiv.inner_map_map,
          TensorProduct.inner_tmul]
      | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]

/-- Product coordinates identify the genuine Hilbert completion with ℓ² on
the product index. Finite sums of the coordinate unit vectors are dense, also
for uncountable index types. -/
def hilbertCoords (e : E ≃ₗᵢ[ℂ] L2 ι) (f : F ≃ₗᵢ[ℂ] L2 κ) :
    HilbertTensor E F ≃ₗᵢ[ℂ] L2 (ι × κ) := by
  classical
  let L := (coordinateIsometry e f).fromCompletion
  refine LinearIsometryEquiv.ofSurjective L fun v => ?_
  have hpure (x : E) (y : F) : L (hilbertTmul x y) = tpPair (e x) (f y) :=
    (coordinateIsometry e f).fromCompletion_apply_coe (x ⊗ₜ[ℂ] y)
  have hsingle (p : ι × κ) : lp.single 2 p (v p) ∈ L.toLinearMap.range := by
    refine ⟨hilbertTmul (e.symm (lp.single 2 p.1 (v p))) (f.symm (lp.single 2 p.2 1)), ?_⟩
    rw [show ∀ z, L.toLinearMap z = L z from fun _ => rfl, hpure]
    simp only [LinearIsometryEquiv.apply_symm_apply]
    apply lp.ext; funext q
    by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2
    · have hpq := Prod.ext h₁ h₂
      simp [hpq, lp.single_apply]
    all_goals
      have hpq : p ≠ q := by intro h; subst q; simp_all
      simp [tpPair_apply, lp.single_apply, hpq.symm, h₁, h₂]
  have hclosed := L.isometry.isClosedEmbedding.isClosed_range
  exact hclosed.mem_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top v)
    (Filter.Eventually.of_forall fun s => L.toLinearMap.range.sum_mem fun p _ => hsingle p)

@[simp] theorem hilbertCoords_tmul (e : E ≃ₗᵢ[ℂ] L2 ι) (f : F ≃ₗᵢ[ℂ] L2 κ) (x : E) (y : F) :
    hilbertCoords e f (hilbertTmul x y) = tpPair (e x) (f y) :=
  (coordinateIsometry e f).fromCompletion_apply_coe (x ⊗ₜ[ℂ] y)

theorem hilbertCoords_swap (e : E ≃ₗᵢ[ℂ] L2 ι) (v : HilbertSquare E) :
    hilbertCoords e e ((hilbertTensorSquare E).swap v) =
      (lpTensorSquare ι).swap (hilbertCoords e e v) := by
  refine hilbertTensor_induction
    (p := fun w => hilbertCoords e e ((hilbertTensorSquare E).swap w) =
      (lpTensorSquare ι).swap (hilbertCoords e e w))
    (isClosed_eq ((hilbertCoords e e).continuous.comp (hilbertTensorSquare E).swap.continuous)
      ((lpTensorSquare ι).swap.continuous.comp (hilbertCoords e e).continuous)) ?_ ?_ v
  · intro x y
    change hilbertCoords e e (hilbertSwap (hilbertTmul x y)) = _
    rw [hilbertSwap_tmul, hilbertCoords_tmul, hilbertCoords_tmul]
    exact ((lpTensorSquare ι).swap_tp (e x) (e y)).symm
  · intro a b ha hb
    simp only [map_add, ha, hb]

end
end GaussianTesting
