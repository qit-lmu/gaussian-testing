module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Fidelity with a class of pure states

Equation (3.2) of the manuscript takes the supremum of the absolute overlaps
with the unit vectors in a nonempty class. The fidelity itself is unsquared.
-/

@[expose] public section

namespace GaussianTesting

/-- The normalized states accepted with probability one, the set 𝒢 in Eq. (3.2). -/
def certaintyStates {E : Type*} [Norm E] (p : E → ℝ) : Set E :=
  {φ | ‖φ‖ = 1 ∧ p φ = 1}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G : Set H} {ψ φ : H}

/-- Fidelity with the class `G`, as in Eq. (3.2) (`eq:define-F-and-G`).
For pure states, `ψ` and the elements of `G` are unit vectors and `G` is nonempty. -/
noncomputable def pureFidelity (G : Set H) (ψ : H) : ℝ :=
  sSup ((fun φ => ‖inner ℂ ψ φ‖) '' G)

private theorem overlaps_bddAbove (hG : ∀ φ ∈ G, ‖φ‖ = 1) :
    BddAbove ((fun φ => ‖inner ℂ ψ φ‖) '' G) := by
  refine ⟨‖ψ‖, ?_⟩
  rintro _ ⟨φ, hφ, rfl⟩
  simpa [hG φ hφ] using norm_inner_le_norm (𝕜 := ℂ) ψ φ

/-- Each comparison state in a class of unit vectors gives a lower bound on fidelity. -/
theorem overlap_le_pureFidelity (hG : ∀ φ ∈ G, ‖φ‖ = 1) (hφ : φ ∈ G) :
    ‖inner ℂ ψ φ‖ ≤ pureFidelity G ψ :=
  le_csSup (overlaps_bddAbove hG) ⟨φ, hφ, rfl⟩

theorem pureFidelity_nonneg (hne : G.Nonempty) (hG : ∀ φ ∈ G, ‖φ‖ = 1) :
    0 ≤ pureFidelity G ψ := by
  obtain ⟨φ, hφ⟩ := hne
  exact (norm_nonneg _).trans (overlap_le_pureFidelity hG hφ)

theorem pureFidelity_le_one (hne : G.Nonempty) (hG : ∀ φ ∈ G, ‖φ‖ = 1)
    (hψ : ‖ψ‖ = 1) : pureFidelity G ψ ≤ 1 := by
  apply csSup_le (hne.image _)
  rintro _ ⟨φ, hφ, rfl⟩
  simpa [hψ, hG φ hφ] using norm_inner_le_norm (𝕜 := ℂ) ψ φ

/-- Squaring the witness inequality gives the comparison used in Theorem 6.4. -/
theorem sq_overlap_le_pureFidelity_sq (hG : ∀ φ ∈ G, ‖φ‖ = 1) (hφ : φ ∈ G) :
    ‖inner ℂ ψ φ‖ ^ 2 ≤ pureFidelity G ψ ^ 2 :=
  (sq_le_sq₀ (norm_nonneg _) (pureFidelity_nonneg ⟨φ, hφ⟩ hG)).mpr
    (overlap_le_pureFidelity hG hφ)

/-- The pointwise squared-overlap promise in Theorem 1.1 is exactly the
bound on squared class fidelity used in the testing corollaries. -/
theorem pureFidelity_sq_le_iff (hne : G.Nonempty) (hG : ∀ φ ∈ G, ‖φ‖ = 1)
    (r : ℝ) :
    pureFidelity G ψ ^ 2 ≤ r ↔ ∀ φ ∈ G, ‖inner ℂ ψ φ‖ ^ 2 ≤ r := by
  constructor
  · intro h φ hφ
    exact (sq_overlap_le_pureFidelity_sq hG hφ).trans h
  · intro h
    have hr : 0 ≤ r := (sq_nonneg _).trans (h hne.some hne.some_mem)
    have hF : pureFidelity G ψ ≤ Real.sqrt r := by
      apply csSup_le (hne.image _)
      rintro _ ⟨χ, hχ, rfl⟩
      exact Real.le_sqrt_of_sq_le (h χ hχ)
    calc
      pureFidelity G ψ ^ 2 ≤ (Real.sqrt r) ^ 2 :=
        (sq_le_sq₀ (pureFidelity_nonneg hne hG) (Real.sqrt_nonneg r)).mpr hF
      _ = r := Real.sq_sqrt hr

/-- Changing the phase of the input does not change its fidelity. -/
theorem pureFidelity_phase (G : Set H) (ψ : H) {z : ℂ} (hz : ‖z‖ = 1) :
    pureFidelity G (z • ψ) = pureFidelity G ψ := by
  simp [pureFidelity, inner_smul_left, hz]

end GaussianTesting
