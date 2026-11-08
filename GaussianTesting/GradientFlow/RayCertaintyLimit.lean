module

public import GaussianTesting.GradientFlow.RayDifferential

@[expose] public section

/-! # Cauchy trajectories and their certainty limits

In the proof of Theorem 3.4, the path-length estimate bounds the distance
between two future rays by the half-arcsine potential at the earlier ray.
Acceptance tending to one makes this bound vanish. Completeness of the
Fubini–Study metric gives a limiting ray, and continuity of acceptance
identifies that limit as a certainty state.
-/

namespace GaussianTesting.TensorSquare

open Set Filter Topology

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K} {ρ : ℝ → Projectivization ℂ H}

/-- Acceptance is continuous on projective Hilbert space. The local normalized
representatives compute the same acceptance on every phase of a ray. -/
theorem continuous_rayAcceptance (hP : T.IsAcceptance P) : Continuous (T.rayAcceptance P) := by
  apply isQuotientMap_rayMk.continuous_iff.mpr
  have hfun : T.rayAcceptance P ∘ (Projectivization.mk' ℂ) =
      (fun x : {v : H // v ≠ 0} => T.accProbA P (rayChartSection x)) := by
    funext x
    exact T.rayAcceptance_mk_eq_accProbA_rayChartSection P x x.property
  rw [hfun]
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (T.hasFDerivAt_accProbA hP (rayChartSection x)).continuousAt.comp
    (f := fun y : {v : H // v ≠ 0} => rayChartSection (y : H))
    ((contDiffAt_rayChartSection (x : H) x.property).continuousAt.comp continuous_subtype_val.continuousAt)

omit [CompleteSpace H] [CompleteSpace K] in
/-- A vanishing path-length bound makes the forward ray trajectory Cauchy. -/
theorem cauchy_ray_of_dist_le_potential {c : ℝ} (_hc : c < 1)
    (hp : Tendsto (fun t => T.rayAcceptance P (ρ t)) atTop (𝓝 1))
    (hbound : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      dist (ρ s) (ρ t) ≤ Vpot c (T.rayAcceptance P (ρ s))) :
    Cauchy (map ρ atTop) := by
  have hV : Continuous (Vpot c) := by unfold Vpot; fun_prop
  have hzero : Tendsto (fun t => Vpot c (T.rayAcceptance P (ρ t))) atTop (𝓝 0) := by
    simpa only [Vpot_one, Function.comp_def] using hV.continuousAt.tendsto.comp hp
  change CauchySeq ρ
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hzero.eventually (Iio_mem_nhds hε))
  refine ⟨max N 0, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact (hbound s t ((le_max_right N 0).trans hs) hst).trans_lt
      (hN s ((le_max_left N 0).trans hs))
  · rw [dist_comm]
    exact (hbound t s ((le_max_right N 0).trans ht) hts).trans_lt
      (hN t ((le_max_left N 0).trans ht))

/-- Completeness gives a limit of the projective trajectory. Its acceptance
is one, and its distance from each forward ray obeys the same potential bound. -/
theorem exists_certainty_limit_of_dist_le_potential (hP : T.IsAcceptance P)
    {c : ℝ} (hc : c < 1)
    (hp : Tendsto (fun t => T.rayAcceptance P (ρ t)) atTop (𝓝 1))
    (hbound : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      dist (ρ s) (ρ t) ≤ Vpot c (T.rayAcceptance P (ρ s))) :
    ∃ q : Projectivization ℂ H, Tendsto ρ atTop (𝓝 q) ∧ T.rayAcceptance P q = 1 ∧
      ∀ s ≥ 0, dist (ρ s) q ≤ Vpot c (T.rayAcceptance P (ρ s)) := by
  obtain ⟨q, hq⟩ := cauchy_map_iff_exists_tendsto.mp (cauchy_ray_of_dist_le_potential hc hp hbound)
  refine ⟨q, hq, tendsto_nhds_unique ((continuous_rayAcceptance hP).tendsto q |>.comp hq) hp, ?_⟩
  intro s hs
  exact le_of_tendsto ((tendsto_const_nhds (x := ρ s)).dist hq)
    (eventually_ge_atTop s |>.mono fun t ht => hbound s t hs ht)

end GaussianTesting.TensorSquare
