module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberLadder
public import GaussianTesting.Bosons.ClosedLambda
public import GaussianTesting.Bosons.SchrodingerLambda
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

@[expose] public section

/-! # Two-copy Fock coordinates for the physical Schrödinger generator -/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Pair occupation vectors and occupations of the two-copy mode set are equivalent. -/
def pairOccupationEquiv (m : ℕ) :
    ((Fin m → ℕ) × (Fin m → ℕ)) ≃ ((Fin 2 × Fin m) → ℕ) where
  toFun p i := if i.1 = 0 then p.1 i.2 else p.2 i.2
  invFun n := (fun j => n (0,j), fun j => n (1,j))
  left_inv p := by ext j <;> simp
  right_inv n := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;> simp

@[simp] theorem pairOccupationEquiv_zero (m : ℕ) (p : (Fin m → ℕ) × (Fin m → ℕ))
    (j : Fin m) : pairOccupationEquiv m p (0,j) = p.1 j := rfl

@[simp] theorem pairOccupationEquiv_one (m : ℕ) (p : (Fin m → ℕ) × (Fin m → ℕ))
    (j : Fin m) : pairOccupationEquiv m p (1,j) = p.2 j := rfl

/-- The number basis indexed in the same pair coordinates as the algebraic generator. -/
def schrodingerPairNumberBasis (m : ℕ) :
    HilbertBasis ((Fin m → ℕ) × (Fin m → ℕ)) ℂ (SchrodingerSpace m) :=
  HilbertBasis.mk (orthonormal_schrodingerNumberVector.comp
    (pairOccupationEquiv m) (pairOccupationEquiv m).injective) (by
      have h := (pairOccupationEquiv m).surjective.range_comp
        (schrodingerNumberVector (σ := Fin 2 × Fin m))
      rw [h, dense_span_schrodingerNumberVector])

@[simp] theorem schrodingerPairNumberBasis_apply (m : ℕ)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    schrodingerPairNumberBasis m p = schrodingerNumberVector (pairOccupationEquiv m p) := by
  exact congrFun (HilbertBasis.coe_mk _ _) p

/-- The actual two-copy unitary from occupation coefficients to wavefunctions. -/
def fockPairSchrodingerEquiv (m : ℕ) : FockB2 m ≃ₗᵢ[ℂ] SchrodingerSpace m :=
  (schrodingerPairNumberBasis m).repr.symm

@[simp] theorem fockPairSchrodingerEquiv_single (m : ℕ)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    fockPairSchrodingerEquiv m (lp.single 2 p 1) =
      schrodingerNumberVector (pairOccupationEquiv m p) := by
  classical
  exact ((schrodingerPairNumberBasis m).repr_symm_single p).trans
    (schrodingerPairNumberBasis_apply m p)

/-- Finite occupation coefficients give their normalized creation-polynomial expansion. -/
def pairNumberPolynomialLinear (m : ℕ) :
    FA2 m →ₗ[ℂ] MvPolynomial (Fin 2 × Fin m) ℂ :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (schrodingerNumberPolynomial (pairOccupationEquiv m p))

@[simp] theorem pairNumberPolynomialLinear_single (m : ℕ)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) (c : ℂ) :
    pairNumberPolynomialLinear m (Finsupp.single p c) =
      c • schrodingerNumberPolynomial (pairOccupationEquiv m p) := by
  simp [pairNumberPolynomialLinear, Finsupp.lsum_single]

/-- The coefficient unitary realizes finite vectors by the specified polynomial Gaussians. -/
theorem fockPairSchrodingerEquiv_embedFA2 (m : ℕ) (f : FA2 m) :
    fockPairSchrodingerEquiv m (embedFA2 f) =
      polynomialGaussian (pairNumberPolynomialLinear m f) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero =>
    have h : embedFA2 (0 : FA2 m) = 0 := by ext p; simp
    simp only [h, map_zero]
    exact (map_zero polynomialGaussianLinear).symm
  | add f g hf hg =>
    simp only [embedFA2_add, map_add, hf, hg, polynomialGaussian_add]
  | single p c =>
    rw [← Finsupp.smul_single_one p c, embedFA2_smul, map_smul,
      map_smul, polynomialGaussian_smul]
    congr 1
    have h : embedFA2 (Finsupp.single p (1 : ℂ)) = lp.single 2 p 1 := by
      apply lp.ext
      funext q
      simp [lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
    rw [h, fockPairSchrodingerEquiv_single, pairNumberPolynomialLinear_single,
      one_smul, polynomialGaussian_schrodingerNumberPolynomial]

theorem pairNumberPolynomialLinear_range (m : ℕ) :
    LinearMap.range (pairNumberPolynomialLinear m) = finiteFockPolynomialCore m := by
  have he (p : (Fin m → ℕ) × (Fin m → ℕ)) :
      schrodingerNumberPolynomial (pairOccupationEquiv m p) =
        fockNumberPolynomial m (pairOccupationEquiv m p) := by
    simp only [schrodingerNumberPolynomial, numberNormalization, fockNumberPolynomial,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  apply le_antisymm
  · rintro p ⟨f,rfl⟩
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simpa only [map_add] using
        (finiteFockPolynomialCore m).add_mem hf hg
    | single p c =>
      rw [pairNumberPolynomialLinear_single, he]
      exact (finiteFockPolynomialCore m).smul_mem c (Submodule.subset_span ⟨_,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro p ⟨n,rfl⟩
    refine ⟨Finsupp.single ((pairOccupationEquiv m).symm n) 1, ?_⟩
    rw [pairNumberPolynomialLinear_single, one_smul, he,
      (pairOccupationEquiv m).apply_symm_apply]

theorem pairOccupationEquiv_update_left (m : ℕ)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) (j : Fin m) (a : ℕ) :
    pairOccupationEquiv m (Function.update p.1 j a, p.2) =
      Function.update (pairOccupationEquiv m p) (0,j) a := by
  funext i
  rcases i with ⟨i,k⟩
  fin_cases i <;> simp [pairOccupationEquiv, Function.update_apply]

theorem pairOccupationEquiv_update_right (m : ℕ)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) (j : Fin m) (a : ℕ) :
    pairOccupationEquiv m (p.1, Function.update p.2 j a) =
      Function.update (pairOccupationEquiv m p) (1,j) a := by
  funext i
  rcases i with ⟨i,k⟩
  fin_cases i <;> simp [pairOccupationEquiv, Function.update_apply]

/-- The first-copy annihilation operator agrees with the actual polynomial action. -/
theorem pairNumberPolynomialLinear_copyL_aF (m : ℕ) (j : Fin m) (f : FA2 m) :
    pairNumberPolynomialLinear m (copyL (aF j) f) =
      polynomialAnnihilation (0,j) (pairNumberPolynomialLinear m f) := by
  have he : (pairNumberPolynomialLinear m).comp (copyL (aF j)) =
      (polynomialAnnihilation (0,j)).comp (pairNumberPolynomialLinear m) := by
    apply Finsupp.lhom_ext
    intro p c
    simp only [LinearMap.comp_apply, copyL, aF, Finsupp.lsum_single,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
      map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      pairNumberPolynomialLinear_single, polynomialAnnihilation_schrodingerNumberPolynomial,
      pairOccupationEquiv_zero, ← pairOccupationEquiv_update_left, smul_smul]
    congr 1
    ring
  exact LinearMap.congr_fun he f

/-- The first-copy creation operator agrees with the actual polynomial action. -/
theorem pairNumberPolynomialLinear_copyL_adF (m : ℕ) (j : Fin m) (f : FA2 m) :
    pairNumberPolynomialLinear m (copyL (adF j) f) =
      polynomialCreation (0,j) (pairNumberPolynomialLinear m f) := by
  have he : (pairNumberPolynomialLinear m).comp (copyL (adF j)) =
      (polynomialCreation (0,j)).comp (pairNumberPolynomialLinear m) := by
    apply Finsupp.lhom_ext
    intro p c
    simp only [LinearMap.comp_apply, copyL, adF, Finsupp.lsum_single,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
      map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      pairNumberPolynomialLinear_single, polynomialCreation_schrodingerNumberPolynomial,
      pairOccupationEquiv_zero, ← pairOccupationEquiv_update_left, smul_smul]
    congr 1
    ring
  exact LinearMap.congr_fun he f

/-- The second-copy annihilation operator agrees with the actual polynomial action. -/
theorem pairNumberPolynomialLinear_copyR_aF (m : ℕ) (j : Fin m) (f : FA2 m) :
    pairNumberPolynomialLinear m (copyR (aF j) f) =
      polynomialAnnihilation (1,j) (pairNumberPolynomialLinear m f) := by
  have he : (pairNumberPolynomialLinear m).comp (copyR (aF j)) =
      (polynomialAnnihilation (1,j)).comp (pairNumberPolynomialLinear m) := by
    apply Finsupp.lhom_ext
    intro p c
    simp only [LinearMap.comp_apply, copyR, aF, Finsupp.lsum_single,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
      map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      pairNumberPolynomialLinear_single, polynomialAnnihilation_schrodingerNumberPolynomial,
      pairOccupationEquiv_one, ← pairOccupationEquiv_update_right, smul_smul]
    congr 1
    ring
  exact LinearMap.congr_fun he f

/-- The second-copy creation operator agrees with the actual polynomial action. -/
theorem pairNumberPolynomialLinear_copyR_adF (m : ℕ) (j : Fin m) (f : FA2 m) :
    pairNumberPolynomialLinear m (copyR (adF j) f) =
      polynomialCreation (1,j) (pairNumberPolynomialLinear m f) := by
  have he : (pairNumberPolynomialLinear m).comp (copyR (adF j)) =
      (polynomialCreation (1,j)).comp (pairNumberPolynomialLinear m) := by
    apply Finsupp.lhom_ext
    intro p c
    simp only [LinearMap.comp_apply, copyR, adF, Finsupp.lsum_single,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
      map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      pairNumberPolynomialLinear_single, polynomialCreation_schrodingerNumberPolynomial,
      pairOccupationEquiv_one, ← pairOccupationEquiv_update_right, smul_smul]
    congr 1
    ring
  exact LinearMap.congr_fun he f

/-- The number-basis generator and physical differential generator agree on their finite core. -/
theorem pairNumberPolynomialLinear_lambda (m : ℕ) (f : FA2 m) :
    pairNumberPolynomialLinear m (lambdaB m f) =
      polynomialLambda m (pairNumberPolynomialLinear m f) := by
  change pairNumberPolynomialLinear m
    ((Complex.I • ∑ j : Fin m,
      (copyL (aF j) ∘ₗ copyR (adF j) - copyL (adF j) ∘ₗ copyR (aF j))) f) = _
  simp only [polynomialLambda, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, map_smul, map_sum, map_sub,
    pairNumberPolynomialLinear_copyL_aF, pairNumberPolynomialLinear_copyL_adF,
    pairNumberPolynomialLinear_copyR_aF, pairNumberPolynomialLinear_copyR_adF]

/-- Applying the physical coordinate unitary to both coordinates of an operator graph. -/
def fockPairGraphEquiv (m : ℕ) :
    (FockB2 m × FockB2 m) ≃L[ℂ] (SchrodingerSpace m × SchrodingerSpace m) :=
  (fockPairSchrodingerEquiv m).toContinuousLinearEquiv.prodCongr
    (fockPairSchrodingerEquiv m).toContinuousLinearEquiv

/-- The actual physical finite-core graph is exactly the image of the coefficient graph. -/
theorem fockPairGraphEquiv_finiteGraph (m : ℕ) :
    (lambdaFiniteGraph m).map (fockPairGraphEquiv m).toLinearMap =
      schrodingerFiniteFockGraph m := by
  apply le_antisymm
  · rintro z ⟨w, ⟨f,rfl⟩, rfl⟩
    have hp : pairNumberPolynomialLinear m f ∈ finiteFockPolynomialCore m := by
      rw [← pairNumberPolynomialLinear_range]
      exact ⟨f,rfl⟩
    refine ⟨⟨pairNumberPolynomialLinear m f, hp⟩, ?_⟩
    change (polynomialGaussian (pairNumberPolynomialLinear m f),
      polynomialGaussian (polynomialLambda m (pairNumberPolynomialLinear m f))) =
        (fockPairSchrodingerEquiv m (embedFA2 f),
          fockPairSchrodingerEquiv m (embedFA2 (lambdaB m f)))
    rw [fockPairSchrodingerEquiv_embedFA2, fockPairSchrodingerEquiv_embedFA2,
      pairNumberPolynomialLinear_lambda]
  · rintro z ⟨p,rfl⟩
    have hp : (p : MvPolynomial (Fin 2 × Fin m) ℂ) ∈
        LinearMap.range (pairNumberPolynomialLinear m) := by
      rw [pairNumberPolynomialLinear_range]
      exact p.property
    obtain ⟨f,hf⟩ := hp
    refine ⟨(embedFA2 f, embedFA2 (lambdaB m f)), mem_lambdaFiniteGraph f, ?_⟩
    change (fockPairSchrodingerEquiv m (embedFA2 f),
        fockPairSchrodingerEquiv m (embedFA2 (lambdaB m f))) =
      (polynomialGaussian p, polynomialGaussian (polynomialLambda m p))
    rw [fockPairSchrodingerEquiv_embedFA2, fockPairSchrodingerEquiv_embedFA2,
      pairNumberPolynomialLinear_lambda, hf]

/-- Unitary transport identifies the manuscript's two graph closures, with their exact domains. -/
theorem fockPairGraphEquiv_closedGraph (m : ℕ) :
    ((closedLambdaB m).graph).map (fockPairGraphEquiv m).toLinearMap =
      (schrodingerLambda m).graph := by
  rw [closedLambdaB_graph, schrodingerLambda_graph]
  have he : ((lambdaFiniteGraph m).topologicalClosure).map
      (fockPairGraphEquiv m).toLinearMap =
        ((lambdaFiniteGraph m).map (fockPairGraphEquiv m).toLinearMap).topologicalClosure := by
    apply SetLike.coe_injective
    exact (fockPairGraphEquiv m).image_closure (lambdaFiniteGraph m : Set _)
  rw [he, fockPairGraphEquiv_finiteGraph]

/-- A coefficient-space graph pair corresponds to exactly the same physical graph pair. -/
theorem fockPairSchrodingerEquiv_mem_graph_iff (m : ℕ) (f g : FockB2 m) :
    (fockPairSchrodingerEquiv m f, fockPairSchrodingerEquiv m g) ∈
      (schrodingerLambda m).graph ↔ (f,g) ∈ (closedLambdaB m).graph := by
  rw [← fockPairGraphEquiv_closedGraph]
  change fockPairGraphEquiv m (f,g) ∈
    ((closedLambdaB m).graph).map (fockPairGraphEquiv m).toLinearMap ↔ _
  constructor
  · rintro ⟨x,hx,he⟩
    have h := (fockPairGraphEquiv m).injective he
    change x ∈ (closedLambdaB m).graph at hx
    exact h ▸ hx
  · intro h
    exact ⟨(f,g),h,rfl⟩

/-- The physical closed generator and occupation generator have the same kernel under the unitary. -/
theorem fockPairSchrodingerEquiv_mem_kernel_iff (m : ℕ) (f : FockB2 m) :
    fockPairSchrodingerEquiv m f ∈ (schrodingerLambda m).ker ↔
      f ∈ (closedLambdaB m).ker := by
  have h := fockPairSchrodingerEquiv_mem_graph_iff m f 0
  simpa only [map_zero, LinearPMap.mem_graph_iff, LinearPMap.mem_ker_iff,
    eq_comm] using h

/-- The closed-generator kernels correspond exactly under the physical unitary. -/
theorem fockPairSchrodingerEquiv_kernel (m : ℕ) :
    ((closedLambdaB m).ker).map (fockPairSchrodingerEquiv m).toLinearMap =
      (schrodingerLambda m).ker := by
  ext g
  constructor
  · rintro ⟨f,hf,rfl⟩
    exact (fockPairSchrodingerEquiv_mem_kernel_iff m f).mpr hf
  · intro hg
    refine ⟨(fockPairSchrodingerEquiv m).symm g, ?_,
      (fockPairSchrodingerEquiv m).apply_symm_apply g⟩
    apply (fockPairSchrodingerEquiv_mem_kernel_iff m _).mp
    simpa using hg

/-- The accepting projection in the number model is exactly the physical kernel projection. -/
theorem fockPairSchrodingerEquiv_P0B (m : ℕ) (f : FockB2 m) :
    fockPairSchrodingerEquiv m (P0B m f) =
      schrodingerP0 m (fockPairSchrodingerEquiv m f) := by
  change _ = (schrodingerLambda m).ker.starProjection _
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (fockPairSchrodingerEquiv_mem_kernel_iff m _).mpr
    rw [P0B_eq_closedLambdaB_kernelProjection]
    exact (closedLambdaB m).ker.starProjection_apply_mem f
  · intro w hw
    obtain ⟨v,rfl⟩ := (fockPairSchrodingerEquiv m).surjective w
    have hv := (fockPairSchrodingerEquiv_mem_kernel_iff m v).mp hw
    rw [← map_sub, (fockPairSchrodingerEquiv m).inner_map_map,
      P0B_eq_closedLambdaB_kernelProjection]
    exact Submodule.starProjection_inner_eq_zero _ _ hv

end
end GaussianTesting
