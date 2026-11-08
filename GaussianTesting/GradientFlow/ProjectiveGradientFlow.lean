module

public import GaussianTesting.GradientFlow.ProjectiveEnergy
public import GaussianTesting.GradientFlow.ProjectiveContinuation
public import GaussianTesting.GradientFlow.HilbertTensor

@[expose] public section

/-!
# Lemma 3.1: the gradient flow on the space of rays

The ODE is imposed on ray curves in affine charts. Local solutions from an
initial ray agree on overlaps. The energy estimate forces every finite-time
trajectory to have a limit in the complete Fubini–Study metric, and the chart
ODE restarts there. Gluing the compatible solutions therefore covers all forward
times. Smoothness is in time in each chart, including at time zero.
-/

namespace GaussianTesting

open Set Filter Topology
open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Smoothness of a ray curve in the affine charts, relative to its time domain. -/
def SmoothRayCurveOn (ρ : ℝ → Projectivization ℂ H) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ u : H, ρ t ∈ rayChartDomain u →
    ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun r => rayChart u (ρ r)) s t

namespace TensorSquare

variable [CompleteSpace H] [CompleteSpace K] {T : TensorSquare H K} {P : K →L[ℂ] K}

/-- A ray trajectory has a limit at each putative finite endpoint, and the
ODE extends smoothly past that ray while preserving the original trajectory. -/
theorem IsProjectiveFlowOn.continue_at_finite_time {ρ : ℝ → Projectivization ℂ H} {a b : ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ (Ico a b)) (hP : T.IsAcceptance P) (hab : a < b) :
    ∃ q, Tendsto ρ (𝓝[<] b) (𝓝 q) ∧ ∃ c > b, ∃ η, EqOn ρ η (Ico a b) ∧
      η b = q ∧ T.IsProjectiveFlowOn P η (Icc a c) := by
  obtain ⟨q, hlim⟩ := hρ.exists_limit_Ico hP hab
  exact ⟨q, hlim, hρ.exists_extension_of_limit_Ico hP hab hlim⟩

omit [CompleteSpace K] in
private theorem projectiveFlow_of_local {ρ : ℝ → Projectivization ℂ H} {D : Set ℝ}
    (h : ∀ t ∈ D, ∃ b : ℝ, t ∈ Ico 0 b ∧ Ico 0 b ∈ 𝓝[D] t ∧
      ∃ η, T.IsProjectiveFlowOn P η (Ico 0 b) ∧ EqOn ρ η (Ico 0 b)) :
    T.IsProjectiveFlowOn P ρ D := by
  constructor
  · intro t ht
    obtain ⟨b, htI, hnear, η, hη, he⟩ := h t ht
    exact ((hη.continuous t htI).congr_of_mem he htI).mono_of_mem_nhdsWithin hnear
  · intro t ht u hu
    obtain ⟨b, htI, hnear, η, hη, he⟩ := h t ht
    rw [he htI] at hu ⊢
    exact ((hη.deriv t htI u hu).congr_of_mem (fun r hr => congrArg (rayChart u) (he hr)) htI)
      |>.mono_of_mem_nhdsWithin hnear

/-- Manuscript Lemma 3.1: for each initial ray there is a smooth global solution
of Eq. (3.3), and every projective solution with that initial ray agrees with it
throughout the forward time domain. -/
theorem exists_unique_smooth_projectiveFlow (hP : T.IsAcceptance P) (q : Projectivization ℂ H) :
    ∃ ρ : ℝ → Projectivization ℂ H, ρ 0 = q ∧
      T.IsProjectiveFlowOn P ρ (Ici 0) ∧ SmoothRayCurveOn ρ (Ici 0) ∧
      ∀ σ : ℝ → Projectivization ℂ H, σ 0 = q → T.IsProjectiveFlowOn P σ (Ici 0) →
        EqOn σ ρ (Ici 0) := by
  obtain ⟨δ, hδ, ξ, hξ0, hξ⟩ := exists_local_projectiveFlow hP 0 q
  obtain ⟨ρ, h0, hρ⟩ := exists_global_of_finite_extension (T.IsProjectiveFlowOn P) q
    ⟨δ, hδ, ξ, hξ0, hξ.mono Ico_subset_Icc_self⟩
    (fun hf hg hfI hgI he => hf.eqOn_Icc hg hfI hgI he)
    projectiveFlow_of_local (by
      intro b η hb hη
      obtain ⟨_, _, c, hc, ζ, he, _, hz⟩ := hη.continue_at_finite_time hP hb
      exact ⟨c, hc, ζ, he, hz.mono Ico_subset_Icc_self⟩)
  refine ⟨ρ, h0, hρ, fun t ht u hu => hρ.contDiffWithinAt_chart_Ici ht hu,
    fun σ hσ0 hσ t ht => ?_⟩
  exact (hσ.eqOn_Icc hρ (a := 0) (b := t) Icc_subset_Ici_self Icc_subset_Ici_self
    (hσ0.trans h0.symm)) (right_mem_Icc.mpr ht)

end TensorSquare

/-- Lemma 3.1 for a swap-commuting orthogonal projection on the completed
Hilbert tensor square: there is a unique smooth forward integral curve from
each initial ray. Uniqueness is on $[0,\infty)$, the domain of the ODE. -/
theorem projective_gradient_flow [CompleteSpace H] {P : HilbertSquare H →L[ℂ] HilbertSquare H}
    (hP : (hilbertTensorSquare H).IsAcceptance P) (q : Projectivization ℂ H) :
    ∃ ρ : ℝ → Projectivization ℂ H, ρ 0 = q ∧
      (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0) ∧ SmoothRayCurveOn ρ (Ici 0) ∧
      ∀ σ : ℝ → Projectivization ℂ H, σ 0 = q →
        (hilbertTensorSquare H).IsProjectiveFlowOn P σ (Ici 0) → EqOn σ ρ (Ici 0) :=
  TensorSquare.exists_unique_smooth_projectiveFlow hP q

end GaussianTesting
