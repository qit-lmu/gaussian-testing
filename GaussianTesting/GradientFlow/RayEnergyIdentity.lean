module

public import GaussianTesting.GradientFlow.ProjectiveEnergy
public import GaussianTesting.GradientFlow.RaySpeed

@[expose] public section

/-!
# The differential energy identity on rays

Along a solution in projective charts, acceptance has time derivative equal
to the squared norm of the horizontal gradient. On each closed interval,
the unit lift supplies this identity, including the one-sided derivatives at
its endpoints. Both sides are independent of the phase of the representative.
-/

namespace GaussianTesting.TensorSquare

open Set Filter Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K} {ρ : ℝ → Projectivization ℂ H}

/-- Squared norm of the horizontal field of Eq. (3.4) at a ray. -/
def rayGradientNormSq (T : TensorSquare H K) (P : K →L[ℂ] K) (q : Projectivization ℂ H) : ℝ :=
  ‖T.gradAccA P (rayUnitRep q)‖ ^ 2

/-- The squared norm may be computed using any unit representative. -/
theorem rayGradientNormSq_mk (T : TensorSquare H K) (P : K →L[ℂ] K) (x : H)
    (hx : ‖x‖ = 1) (hn : x ≠ 0) :
    T.rayGradientNormSq P (Projectivization.mk ℂ x hn) = ‖T.gradAccA P x‖ ^ 2 := by
  obtain ⟨z, hz, hrep⟩ := rayUnitRep_phase x hx hn
  rw [rayGradientNormSq, hrep, T.gradAccA_phase P z hz, norm_smul, hz, one_mul]

/-- On each closed subinterval of a ray flow, the derivative of acceptance
within that interval equals the squared horizontal gradient norm. -/
theorem IsProjectiveFlowOn.hasDerivWithinAt_rayAcceptance_Icc {s : Set ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ s) (hP : T.IsAcceptance P)
    {a b t : ℝ} (hI : Icc a b ⊆ s) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun r => T.rayAcceptance P (ρ r))
      (T.rayGradientNormSq P (ρ t)) (Icc a b) t := by
  obtain ⟨γ, _, hγ, hrep⟩ := hρ.exists_unit_lift_Icc hP (ht.1.trans ht.2) hI
    (rayUnitRep (ρ a)) (norm_rayUnitRep _) (fun _ => (mk_rayUnitRep _).symm)
  have hn (r : ℝ) (hr : r ∈ Icc a b) : γ r ≠ 0 := fun h => by simpa [h] using hγ.sphere r hr
  have hgrad : T.rayGradientNormSq P (ρ t) = ‖T.gradAccA P (γ t)‖ ^ 2 := by
    rw [hrep t ht (hn t ht), T.rayGradientNormSq_mk P _ (hγ.sphere t ht)]
  rw [hgrad]
  apply (hγ.hasDerivWithinAt_accProb hP ht).congr_of_mem _ ht
  intro r hr
  rw [hrep r hr (hn r hr), T.rayAcceptance_mk P _ (hγ.sphere r hr)]

/-- The differential energy identity of Eq. (3.7) on a forward half-line.
At its initial time the derivative is taken from the right. -/
theorem IsProjectiveFlowOn.hasDerivWithinAt_rayAcceptance {a t : ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ (Ici a)) (hP : T.IsAcceptance P) (ht : t ∈ Ici a) :
    HasDerivWithinAt (fun r => T.rayAcceptance P (ρ r))
      (T.rayGradientNormSq P (ρ t)) (Ici a) t := by
  have hlt : t < t + 1 := by linarith
  apply (hρ.hasDerivWithinAt_rayAcceptance_Icc hP (Icc_subset_Ici_self : Icc a (t + 1) ⊆ Ici a)
    ⟨ht, hlt.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)]
    with r hr hr' using ⟨hr, hr'.le⟩

/-- Acceptance is nondecreasing along the ray trajectory, without a spectral hypothesis. -/
theorem IsProjectiveFlowOn.rayAcceptance_mono {a : ℝ} (hρ : T.IsProjectiveFlowOn P ρ (Ici a))
    (hP : T.IsAcceptance P) : MonotoneOn (fun r => T.rayAcceptance P (ρ r)) (Ici a) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
  · exact fun t ht => (hρ.hasDerivWithinAt_rayAcceptance hP ht).continuousWithinAt
  · exact fun t ht => (hρ.hasDerivWithinAt_rayAcceptance hP (interior_subset ht)).mono interior_subset
  · exact fun _ _ => sq_nonneg _

/-- The actual speed of the ray trajectory in the Fubini–Study metric is the
norm of its horizontal field. At the initial time this is a right limit. -/
theorem IsProjectiveFlowOn.tendsto_dist_div_time {a t : ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ (Ici a)) (hP : T.IsAcceptance P) (ht : t ∈ Ici a) :
    Tendsto (fun r => dist (ρ r) (ρ t) / |r - t|) (𝓝[Ici a \ {t}] t)
      (𝓝 (Real.sqrt (T.rayGradientNormSq P (ρ t)))) := by
  have hlt : t < t + 1 := by linarith
  have hab : a ≤ t + 1 := ht.trans hlt.le
  let s := Icc a (t + 1)
  have hs : s ⊆ Ici a := Icc_subset_Ici_self
  have hts : t ∈ s := ⟨ht, hlt.le⟩
  obtain ⟨γ, _, hγ, hrep⟩ := hρ.exists_unit_lift_Icc hP hab hs
    (rayUnitRep (ρ a)) (norm_rayUnitRep _) (fun _ => (mk_rayUnitRep _).symm)
  have hspeed := tendsto_dist_div_time_of_horizontal_lift hts (hγ.deriv t hts)
    (T.inner_gradAccA_eq_zero hP (hγ.sphere t hts)) hγ.sphere hrep ((hρ.continuous.mono hs) t hts)
  have hn : γ t ≠ 0 := fun h => by simpa [h] using hγ.sphere t hts
  have hnorm : Real.sqrt (T.rayGradientNormSq P (ρ t)) = ‖T.gradAccA P (γ t)‖ := by
    rw [hrep t hts hn, T.rayGradientNormSq_mk P _ (hγ.sphere t hts), Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm]
  apply hspeed.mono_left (nhdsWithin_le_of_mem (sdiff_mem_nhdsWithin_sdiff _ {t}))
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with r hr hr'
  exact ⟨hr, hr'.le⟩

end
end GaussianTesting.TensorSquare
