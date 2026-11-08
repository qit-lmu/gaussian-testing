module

public import GaussianTesting.GradientFlow.RayGradientBound

@[expose] public section

/-!
# Convergence of acceptance after Eq. (3.7)

Acceptance along a forward projective trajectory is nondecreasing and bounded
by one. If its limit were below one, Eq. (3.7) would give a uniformly positive
lower bound on its derivative, contradicting boundedness. This is the argument
in the paragraph following Eq. (3.7), for arbitrary real forward times.
-/

namespace GaussianTesting

open Set Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : HilbertSquare H →L[ℂ] HilbertSquare H}

/-- Above the spectral threshold, acceptance along any forward ray solution
converges to one as real time tends to infinity. -/
theorem rayAcceptance_tendsto_one (hP : (hilbertTensorSquare H).IsAcceptance P)
    {α : ℝ} (hα : α ∈ Icc 0 1)
    (hspec : spectrum ℂ (threeCopyAverage P) ⊆ Complex.ofReal '' Icc 0 α ∪ {1})
    {ρ : ℝ → Projectivization ℂ H} (hρ : (hilbertTensorSquare H).IsProjectiveFlowOn P ρ (Ici 0))
    (hhigh : 3 / 2 * α < (hilbertTensorSquare H).rayAcceptance P (ρ 0)) :
    Tendsto (fun t => (hilbertTensorSquare H).rayAcceptance P (ρ t)) atTop (𝓝 1) := by
  let p : ℝ → ℝ := fun t => (hilbertTensorSquare H).rayAcceptance P (ρ t)
  have hm : MonotoneOn p (Ici 0) := hρ.rayAcceptance_mono hP
  have hp1 (t : ℝ) : p t ≤ 1 :=
    (hilbertTensorSquare H).accProbA_le_one hP (norm_rayUnitRep _)
  have hmn : Monotone (fun n : ℕ => p n) := by
    intro m n hmn
    exact hm (by simp) (by simp) (by exact_mod_cast hmn)
  have hb : BddAbove (range (fun n : ℕ => p n)) := ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact hp1 n⟩
  let L := ⨆ n : ℕ, p n
  have hL : L ≤ 1 := ciSup_le fun n => hp1 n
  have hpL (t : ℝ) (ht : 0 ≤ t) : p t ≤ L := by
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact (hm ht (by simp) hn).trans (le_ciSup hb n)
  have he : L = 1 := by
    by_contra hne
    have hlt : L < 1 := lt_of_le_of_ne hL hne
    let β := 16 * (p 0 - 3 / 2 * α) * (1 - L)
    have hβ : 0 < β := by dsimp [β, p]; positivity
    have hd (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
        HasDerivWithinAt (fun t => p t - β * t)
          ((hilbertTensorSquare H).rayGradientNormSq P (ρ t) - β) (Ici 0) t := by
      apply (hρ.hasDerivWithinAt_rayAcceptance hP ht).sub
      simpa using ((hasDerivAt_id t).const_mul β).hasDerivWithinAt (s := Ici 0)
    have hg : MonotoneOn (fun t => p t - β * t) (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      · exact fun t ht => (hd t ht).continuousWithinAt
      · exact fun t ht => (hd t (interior_subset ht)).mono interior_subset
      · intro t ht
        have ht' : 0 ≤ t := interior_subset ht
        have hbound := ray_flow_derivative_bounds hP hα hspec hρ ht'
        have hge : 16 * (p 0 - 3 / 2 * α) * (1 - p t) ≤
            (hilbertTensorSquare H).rayGradientNormSq P (ρ t) :=
          hbound.2.2.2.trans hbound.2.2.1
        have hfactor : 0 ≤ 16 * (p 0 - 3 / 2 * α) := by dsimp [p]; positivity
        have hβle : β ≤ 16 * (p 0 - 3 / 2 * α) * (1 - p t) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left (hpL t ht') 1) hfactor
        exact sub_nonneg.mpr (hβle.trans hge)
    let t := (2 - p 0) / β
    have ht : 0 ≤ t := div_nonneg (by linarith [hp1 0]) hβ.le
    have hg' := hg (by simp) ht ht
    have hu := hp1 t
    have he' : β * t = 2 - p 0 := by dsimp [t]; field_simp
    simp only [mul_zero, sub_zero] at hg'
    linarith
  have hnat : Tendsto (fun n : ℕ => p n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [← he] using tendsto_atTop_ciSup hmn hb
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨n, hn⟩ := (hnat.eventually (Ioi_mem_nhds ha)).exists
    filter_upwards [eventually_ge_atTop (n : ℝ)] with t ht
    exact hn.trans_le (hm (by simp) ((Nat.cast_nonneg n).trans ht) ht)
  · intro b hb
    exact Eventually.of_forall fun t => (hp1 t).trans_lt hb

end GaussianTesting
