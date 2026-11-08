module

public import GaussianTesting.GradientFlow.HilbertGradientBound
public import GaussianTesting.GradientFlow.HilbertTensorFour

@[expose] public section

/-!
# The symmetric Hilbert tensor cube

The footnote before Lemma 3.3 restricts the three-copy average to `Sym³(H)`.
On the completed Hilbert tensor cube this is the closed joint fixed space of
the adjacent transpositions `(12)` and `(23)`, which generate all permutations
of the three factors. The swap-commutation assumption on the two-copy test
ensures that its three-copy average preserves this subspace.
-/

namespace GaussianTesting

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exchange the first two factors of the completed Hilbert tensor cube. -/
def cubeSwap12 : HilbertCube H ≃ₗᵢ[ℂ] HilbertCube H :=
  hilbertAssoc.symm.trans
    ((hilbertTensorEquiv hilbertSwap (LinearIsometryEquiv.refl ℂ H)).trans hilbertAssoc)

/-- Exchange the last two factors of the completed Hilbert tensor cube. -/
def cubeSwap23 : HilbertCube H ≃ₗᵢ[ℂ] HilbertCube H :=
  hilbertTensorEquiv (LinearIsometryEquiv.refl ℂ H) hilbertSwap

@[simp] theorem cubeSwap12_tmul (x y z : H) :
    cubeSwap12 (hilbertTmul x (hilbertTmul y z)) =
      hilbertTmul y (hilbertTmul x z) := by
  simp [cubeSwap12]

@[simp] theorem cubeSwap23_tmul (x y z : H) :
    cubeSwap23 (hilbertTmul x (hilbertTmul y z)) =
      hilbertTmul x (hilbertTmul z y) := by
  simp [cubeSwap23]

@[simp] theorem cubeSwap12_apply_apply (v : HilbertCube H) :
    cubeSwap12 (cubeSwap12 v) = v := by
  have h : cubeSwap12.toLinearIsometry.toContinuousLinearMap.comp
      cubeSwap12.toLinearIsometry.toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (HilbertCube H) := by
    apply ContinuousLinearMap.ext_on dense_span_hilbertTriple
    rintro _ ⟨⟨x,y,z⟩,rfl⟩
    simp
  exact DFunLike.congr_fun h v

@[simp] theorem cubeSwap23_apply_apply (v : HilbertCube H) :
    cubeSwap23 (cubeSwap23 v) = v := by
  have h : cubeSwap23.toLinearIsometry.toContinuousLinearMap.comp
      cubeSwap23.toLinearIsometry.toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (HilbertCube H) := by
    apply ContinuousLinearMap.ext_on dense_span_hilbertTriple
    rintro _ ⟨⟨x,y,z⟩,rfl⟩
    simp
  exact DFunLike.congr_fun h v

theorem inner_cubeSwap12_right (u v : HilbertCube H) :
    ⟪u, cubeSwap12 v⟫_ℂ = ⟪cubeSwap12 u, v⟫_ℂ := by
  simpa using (cubeSwap12 (H := H)).inner_map_map (cubeSwap12 u) v

theorem inner_cubeSwap23_right (u v : HilbertCube H) :
    ⟪u, cubeSwap23 v⟫_ℂ = ⟪cubeSwap23 u, v⟫_ℂ := by
  simpa using (cubeSwap23 (H := H)).inner_map_map (cubeSwap23 u) v

/-- `Sym³(H)`: the closed subspace fixed by the two adjacent transpositions. -/
def symmetricCube (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Submodule ℂ (HilbertCube H) :=
  (cubeSwap12.toLinearIsometry.toContinuousLinearMap - ContinuousLinearMap.id ℂ _).ker ⊓
    (cubeSwap23.toLinearIsometry.toContinuousLinearMap - ContinuousLinearMap.id ℂ _).ker

@[simp] theorem mem_symmetricCube (v : HilbertCube H) :
    v ∈ symmetricCube H ↔ cubeSwap12 v = v ∧ cubeSwap23 v = v := by
  simp [symmetricCube, sub_eq_zero]

theorem isClosed_symmetricCube : IsClosed (symmetricCube H : Set (HilbertCube H)) :=
  (cubeSwap12.toLinearIsometry.toContinuousLinearMap -
    ContinuousLinearMap.id ℂ _).isClosed_ker.inter
    (cubeSwap23.toLinearIsometry.toContinuousLinearMap -
      ContinuousLinearMap.id ℂ _).isClosed_ker

instance symmetricCube_completeSpace : CompleteSpace (symmetricCube H) :=
  isClosed_symmetricCube.completeSpace_coe

theorem hilbertTmul_mem_symmetricCube (ψ : H) :
    hilbertTmul ψ (hilbertTmul ψ ψ) ∈ symmetricCube H := by
  simp

private theorem inner_acceptance_swap
    {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) (a b x y : H) :
    ⟪hilbertTmul a b, P (hilbertTmul x y)⟫_ℂ =
      ⟪hilbertTmul b a, P (hilbertTmul y x)⟫_ℂ := by
  have hswap (v : HilbertSquare H) : P (hilbertSwap v) = hilbertSwap (P v) :=
    hP.swap_comm v
  rw [← hilbertSwap_tmul x y, hswap, ← hilbertSwap_tmul a b,
    LinearIsometryEquiv.inner_map_map]

/-- The three-copy average commutes with exchange of the first two copies. -/
theorem threeCopyAverage_cubeSwap12
    {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) (v : HilbertCube H) :
    threeCopyAverage P (cubeSwap12 v) = cubeSwap12 (threeCopyAverage P v) := by
  have he : (threeCopyAverage P).comp cubeSwap12.toLinearIsometry.toContinuousLinearMap =
      cubeSwap12.toLinearIsometry.toContinuousLinearMap.comp (threeCopyAverage P) := by
    apply hilbertCube_operator_ext
    intro a b c x y z
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, cubeSwap12_tmul, inner_cubeSwap12_right]
    simp only [threeCopyAverage, smul_apply, add_apply,
      inner_smul_right, inner_add_right, inner_threeCopyPair12_tmul,
      inner_threeCopyPair13_tmul, inner_threeCopyPair23_tmul]
    rw [inner_acceptance_swap hP a b y x]
    ring
  exact DFunLike.congr_fun he v

/-- The three-copy average commutes with exchange of the last two copies. -/
theorem threeCopyAverage_cubeSwap23
    {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) (v : HilbertCube H) :
    threeCopyAverage P (cubeSwap23 v) = cubeSwap23 (threeCopyAverage P v) := by
  have he : (threeCopyAverage P).comp cubeSwap23.toLinearIsometry.toContinuousLinearMap =
      cubeSwap23.toLinearIsometry.toContinuousLinearMap.comp (threeCopyAverage P) := by
    apply hilbertCube_operator_ext
    intro a b c x y z
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, cubeSwap23_tmul, inner_cubeSwap23_right]
    simp only [threeCopyAverage, smul_apply, add_apply,
      inner_smul_right, inner_add_right, inner_threeCopyPair12_tmul,
      inner_threeCopyPair13_tmul, inner_threeCopyPair23_tmul]
    rw [inner_acceptance_swap hP b c z y]
    ring
  exact DFunLike.congr_fun he v

/-- The three-copy average preserves `Sym³(H)`, as used in the footnote before Lemma 3.3. -/
theorem threeCopyAverage_maps_symmetricCube
    {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) :
    ∀ v ∈ symmetricCube H, threeCopyAverage P v ∈ symmetricCube H := by
  intro v hv
  rw [mem_symmetricCube] at hv ⊢
  constructor
  · rw [← threeCopyAverage_cubeSwap12 hP, hv.1]
  · rw [← threeCopyAverage_cubeSwap23 hP, hv.2]

end
end GaussianTesting
