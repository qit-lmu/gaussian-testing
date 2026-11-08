module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberPolynomial
public import GaussianTesting.Bosons.PolynomialGaussianDensity
public import GaussianTesting.Bosons.SchrodingerLambda

@[expose] public section

/-!
# Density of the manuscript's finite number-vector domain

Ordered creation powers span every polynomial Gaussian. Analytic density
therefore makes the prescribed finite Fock domain, and its graph closure,
dense in the actual Schrödinger Hilbert space.
-/

namespace GaussianTesting

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The finite domain specified by number vectors is the polynomial Gaussian range. -/
theorem schrodingerFiniteLambda_domain_eq_range (m : ℕ) :
    ((schrodingerFiniteLambda m).domain : Set (SchrodingerSpace m)) =
      Set.range (polynomialGaussian (ι := Fin 2 × Fin m)) := by
  ext f
  change f ∈ (schrodingerFiniteLambda m).domain ↔ ∃ p, polynomialGaussian p = f
  rw [schrodingerFiniteLambda_mem_domain, finiteFockPolynomialCore_eq_top]
  simp only [Submodule.mem_top, true_and]

/-- The specified finite number-vector domain is dense, without assuming an
orthonormal-basis identification. -/
theorem schrodingerFiniteLambda_domain_dense (m : ℕ) :
    Dense ((schrodingerFiniteLambda m).domain : Set (SchrodingerSpace m)) := by
  rw [schrodingerFiniteLambda_domain_eq_range]
  exact denseRange_polynomialGaussian

/-- The actual graph-closed generator is densely defined. -/
theorem schrodingerLambda_domain_dense (m : ℕ) :
    Dense ((schrodingerLambda m).domain : Set (SchrodingerSpace m)) := by
  apply (schrodingerFiniteLambda_domain_dense m).mono
  intro f hf
  obtain ⟨p,hp,rfl⟩ := (schrodingerFiniteLambda_mem_domain m f).mp hf
  have hg : (polynomialGaussian p, polynomialGaussian (polynomialLambda m p)) ∈
      (schrodingerLambda m).graph := by
    rw [schrodingerLambda_graph]
    apply (schrodingerFiniteFockGraph m).le_topologicalClosure
    exact ⟨⟨p,hp⟩,rfl⟩
  obtain ⟨x,hx,_⟩ := (schrodingerLambda m).mem_graph_iff.mp hg
  change polynomialGaussian p ∈ (schrodingerLambda m).domain
  simpa only [hx] using x.property

end
end GaussianTesting
