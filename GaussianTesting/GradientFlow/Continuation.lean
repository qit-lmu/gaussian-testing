module

public import GaussianTesting.GradientFlow.LocalFlow
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

@[expose] public section

/-!
# Continuation of a local unit-vector flow at a finite endpoint

In the proof of Lemma 3.1, the distance traveled is bounded by the integral of
speed. The integral Cauchy–Schwarz inequality and the energy identity control
that length on every subinterval. At a finite endpoint the trajectory therefore
has a unit limit, from which the local ODE restarts.
-/

namespace GaussianTesting.TensorSquare

open Filter Set
open scoped Topology

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K} {γ : ℝ → H} {s : Set ℝ}

/-- Integral Cauchy–Schwarz against the constant function on a closed interval,
by integrating the square of a centered multiple of the integrand. -/
private lemma sq_integral_le_length_mul_integral_sq {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  let d := b - a
  let m := ∫ t in a..b, f t
  have hd : 0 < d := sub_pos.mpr hlt
  have hsq : 0 ≤ ∫ t in a..b, (d ^ 2 * (f t) ^ 2 - (2 * d * m) * f t + m ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hab fun t => by nlinarith [sq_nonneg (d * f t - m)]
  have hc₁ := (continuousOn_const.mul (hf.pow 2) : ContinuousOn (fun t => d ^ 2 * f t ^ 2) _)
  have hc₂ := (continuousOn_const.mul hf : ContinuousOn (fun t => (2 * d * m) * f t) _)
  rw [intervalIntegral.integral_add (f := fun t => d ^ 2 * f t ^ 2 - (2 * d * m) * f t)
    (g := fun _ => m ^ 2) ((hc₁.sub hc₂).intervalIntegrable_of_Icc hab)
    intervalIntegrable_const, intervalIntegral.integral_sub (f := fun t => d ^ 2 * f t ^ 2)
    (g := fun t => (2 * d * m) * f t)
    (hc₁.intervalIntegrable_of_Icc hab) (hc₂.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hsq
  change 0 ≤ d ^ 2 * (∫ t in a..b, f t ^ 2) - (2 * d * m) * m + d * m ^ 2 at hsq
  exact (mul_le_mul_iff_right₀ hd).mp (by nlinarith only [hsq] :
    d * m ^ 2 ≤ d * (d * ∫ t in a..b, f t ^ 2))

private lemma IsUnitFlowOn.continuousOn_grad_comp (hγ : T.IsUnitFlowOn P γ s) :
    ContinuousOn (fun t => T.gradAccA P (γ t)) s :=
  (T.contDiff_gradAccA P).continuous.comp_continuousOn
    (fun t ht => (hγ.deriv t ht).continuousWithinAt)

/-- The distance between two points of a local solution is at most the integral of speed. -/
theorem IsUnitFlowOn.dist_le_integral_speed (hγ : T.IsUnitFlowOn P γ s)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    dist (γ a) (γ b) ≤ ∫ t in a..b, ‖T.gradAccA P (γ t)‖ := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt γ (T.gradAccA P (γ t)) t :=
    ((hγ.deriv t (hI (mem_Icc_of_Ioo ht))).mono hI).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [dist_comm, dist_eq_norm]
  exact norm_sub_le_integral_of_norm_deriv_le_of_le hab
    (fun t ht => ((hγ.deriv t (hI ht)).mono hI).continuousWithinAt)
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (.of_forall fun t ht => ((hd t ht).deriv ▸ le_rfl))
    ((hγ.continuousOn_grad_comp.mono hI).norm.intervalIntegrable_of_Icc hab)

/-- Squared path length is bounded by elapsed time times the local increase in acceptance. -/
theorem IsUnitFlowOn.integral_speed_sq_le_energy (hγ : T.IsUnitFlowOn P γ s)
    (hP : T.IsAcceptance P) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    (∫ t in a..b, ‖T.gradAccA P (γ t)‖) ^ 2 ≤
      (b - a) * (T.accProbA P (γ b) - T.accProbA P (γ a)) := by
  rw [← hγ.integral_norm_grad_sq_eq hP hab hI]
  exact sq_integral_le_length_mul_integral_sq hab (hγ.continuousOn_grad_comp.mono hI).norm

/-- The Fubini–Study angle between unit-vector states is at most the integral of speed. -/
theorem IsUnitFlowOn.angle_le_integral_speed (hγ : T.IsUnitFlowOn P γ s)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    Real.arccos ‖inner ℂ (γ a) (γ b)‖ ≤ ∫ t in a..b, ‖T.gradAccA P (γ t)‖ := by
  let speed (t : ℝ) := ‖T.gradAccA P (γ t)‖
  let remaining (t : ℝ) := ∫ r in (a + t)..b, speed r
  have hshift : MapsTo (fun t : ℝ => a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    exact ⟨le_add_of_nonneg_right ht.1, by linarith [ht.2]⟩
  have hint {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
      IntervalIntegrable speed MeasureTheory.volume u v :=
    (hγ.continuousOn_grad_comp.mono ((Icc_subset_Icc hau hvb).trans hI)).norm.intervalIntegrable_of_Icc huv
  have hcont : ContinuousOn γ (Icc a b) :=
    fun t ht => ((hγ.deriv t (hI ht)).mono hI).continuousWithinAt
  have hangle := projective_angle_le_of_chord_bound (γ := fun t => γ (a + t)) (v := remaining)
    (sub_nonneg.mpr hab) (hcont.comp (continuous_const.add continuous_id).continuousOn hshift)
    (fun t ht => hγ.sphere _ (hI (hshift ht))) (by
      intro u hu v hv huv
      have hu' := hshift hu
      have hv' := hshift hv
      have huv' : a + u ≤ a + v := add_le_add_right huv a
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hint hu'.1 huv' hv'.2) (hint hv'.1 hv'.2 le_rfl)
      change ‖γ (a + u) - γ (a + v)‖ ≤
        (∫ r in (a + u)..b, speed r) - ∫ r in (a + v)..b, speed r
      rw [← hadd, add_sub_cancel_right, ← dist_eq_norm]
      exact hγ.dist_le_integral_speed huv' ((Icc_subset_Icc hu'.1 hv'.2).trans hI))
  have hang : Real.arccos ‖inner ℂ (γ a) (γ b)‖ ≤ ∫ t in a..b, speed t := by
    simpa only [remaining, add_zero, show a + (b - a) = b by ring,
      intervalIntegral.integral_same, sub_zero] using hangle
  exact hang

/-- The squared Fubini–Study angle between two unit-vector states is at most
elapsed time times the increase in acceptance (Lemma 3.1). -/
theorem IsUnitFlowOn.angle_sq_le_energy (hγ : T.IsUnitFlowOn P γ s)
    (hP : T.IsAcceptance P) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    (Real.arccos ‖inner ℂ (γ a) (γ b)‖) ^ 2 ≤
      (b - a) * (T.accProbA P (γ b) - T.accProbA P (γ a)) := by
  exact (pow_le_pow_left₀ (Real.arccos_nonneg _) (hγ.angle_le_integral_speed hab hI) 2).trans
    (hγ.integral_speed_sq_le_energy hP hab hI)

/-- Acceptance is in `[0,1]`, hence the squared projective angle is at most
the elapsed time on any closed subinterval of a local flow. -/
theorem IsUnitFlowOn.angle_sq_le_time_sub (hγ : T.IsUnitFlowOn P γ s)
    (hP : T.IsAcceptance P) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    (Real.arccos ‖inner ℂ (γ a) (γ b)‖) ^ 2 ≤ b - a := by
  apply (hγ.angle_sq_le_energy hP hab hI).trans
  exact mul_le_of_le_one_right (sub_nonneg.mpr hab) (by
    linarith [T.accProbA_nonneg hP (γ a),
      T.accProbA_le_one hP (hγ.sphere b (hI (right_mem_Icc.mpr hab)))])

/-- The local unit-vector trajectory satisfies the square-root modulus used at a finite endpoint. -/
theorem IsUnitFlowOn.dist_sq_le_time_sub (hγ : T.IsUnitFlowOn P γ s)
    (hP : T.IsAcceptance P) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    dist (γ a) (γ b) ^ 2 ≤ b - a := by
  calc
    _ ≤ (∫ t in a..b, ‖T.gradAccA P (γ t)‖) ^ 2 :=
      pow_le_pow_left₀ (dist_nonneg) (hγ.dist_le_integral_speed hab hI) 2
    _ ≤ _ := hγ.integral_speed_sq_le_energy hP hab hI
    _ ≤ b - a := mul_le_of_le_one_right (sub_nonneg.mpr hab) (by
      linarith [T.accProbA_nonneg hP (γ a),
        T.accProbA_le_one hP (hγ.sphere b (hI (right_mem_Icc.mpr hab)))])

/-- A unit-vector solution has a unit limit at its finite right endpoint. -/
theorem IsUnitFlowOn.exists_unit_limit_Ico {a b : ℝ} (hγ : T.IsUnitFlowOn P γ (Ico a b))
    (hP : T.IsAcceptance P) (hab : a < b) :
    ∃ x : H, ‖x‖ = 1 ∧ Tendsto γ (𝓝[<] b) (𝓝 x) := by
  have hc : Cauchy (Filter.map γ (𝓝[<] b)) := by
    refine Metric.cauchy_iff.mpr ⟨inferInstance, ?_⟩
    intro ε hε
    let J := Ioo (max a (b - ε ^ 2)) b
    have hJ : J ∈ 𝓝[<] b := Ioo_mem_nhdsLT (max_lt hab (by nlinarith [sq_pos_of_pos hε]))
    refine ⟨γ '' J, image_mem_map hJ, ?_⟩
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have bound {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) (huv : u ≤ v) :
        dist (γ u) (γ v) < ε := by
      have hI : Icc u v ⊆ Ico a b :=
        fun t ht => ⟨(le_max_left _ _).trans (hu.1.le.trans ht.1), ht.2.trans_lt hv.2⟩
      have hnear : b - ε ^ 2 < u := (le_max_right _ _).trans_lt hu.1
      have hdist := hγ.dist_sq_le_time_sub hP huv hI
      have hvb : v < b := hv.2
      nlinarith [dist_nonneg (x := γ u) (y := γ v)]
    rcases le_total u v with huv | hvu
    · exact bound hu hv huv
    · simpa only [dist_comm (γ u) (γ v)] using bound hv hu hvu
  obtain ⟨x, hx⟩ := cauchy_map_iff_exists_tendsto.mp hc
  refine ⟨x, tendsto_nhds_unique_of_eventuallyEq hx.norm tendsto_const_nhds ?_, hx⟩
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht using hγ.sphere t (Ioo_subset_Ico_self ht)

/-- If a solution on a half-open interval converges to its value at the endpoint,
continuity of the field gives the left derivative there. -/
private lemma endpoint_left_deriv {a b : ℝ} (hab : a < b) {η : ℝ → H}
    (hd : ∀ t ∈ Ioo a b, HasDerivAt η (T.gradAccA P (η t)) t)
    (hlim : Tendsto η (𝓝[<] b) (𝓝 (η b))) :
    HasDerivWithinAt η (T.gradAccA P (η b)) (Iic b) b := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo a b)
  · exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  · exact hlim.mono_left (nhdsWithin_mono b Ioo_subset_Iio_self)
  · exact Ioo_mem_nhdsLT hab
  · apply (((T.contDiff_gradAccA P).continuous.continuousAt).tendsto.comp hlim).congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht using (hd t ht).deriv.symm

/-- A local solution extends beyond every finite positive-length time interval.
The new solution agrees on the original half-open interval and satisfies the ODE
also at its former endpoint. -/
theorem IsUnitFlowOn.exists_extension_Ico {a b : ℝ} (hγ : T.IsUnitFlowOn P γ (Ico a b))
    (hP : T.IsAcceptance P) (hab : a < b) :
    ∃ c > b, ∃ η : ℝ → H, EqOn γ η (Ico a b) ∧ T.IsUnitFlowOn P η (Icc a c) := by
  obtain ⟨x, hx, hlim⟩ := hγ.exists_unit_limit_Ico hP hab
  obtain ⟨δ, hδ, hlocal⟩ := T.exists_smooth_local_unitFlow hP
  obtain ⟨ξ, hstart, hξ, _⟩ := hlocal x hx
  let c := b + δ
  have hbc : b < c := lt_add_of_pos_right _ hδ
  let η (t : ℝ) := if t < b then γ t else ξ (t - b)
  have old_eq (t : ℝ) (ht : t < b) : η t = γ t := by simp [η, ht]
  have new_eq (t : ℝ) (ht : b ≤ t) : η t = ξ (t - b) := by simp [η, not_lt.mpr ht]
  have time_shift : MapsTo (fun t : ℝ => t - b) (Icc b c) (Icc 0 δ) := by
    intro t ht
    exact ⟨sub_nonneg.mpr ht.1, sub_le_iff_le_add.mpr (by simpa [c, add_comm] using ht.2)⟩
  have old_deriv (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt η (T.gradAccA P (η t)) (Ico a b) t := by
    rw [old_eq t ht.2]
    exact (hγ.deriv t ht).congr_of_mem (fun u hu => old_eq u hu.2) ht
  have new_deriv (t : ℝ) (ht : t ∈ Icc b c) :
      HasDerivWithinAt η (T.gradAccA P (η t)) (Icc b c) t := by
    rw [new_eq t ht.1]
    have hd := (hξ.deriv (t - b) (time_shift ht)).scomp t
      ((hasDerivAt_id t).sub_const b).hasDerivWithinAt time_shift
    apply (show HasDerivWithinAt (fun u => ξ (u - b)) (T.gradAccA P (ξ (t - b))) (Icc b c) t by
      simpa only [one_smul, Function.comp_def, id_eq] using hd).congr_of_mem
        (fun u hu => new_eq u hu.1) ht
  refine ⟨c, hbc, η, fun t ht => (old_eq t ht.2).symm, ?_⟩
  constructor
  · intro t ht
    by_cases htb : t < b
    · rw [old_eq t htb]
      exact hγ.sphere t ⟨ht.1, htb⟩
    · rw [new_eq t (le_of_not_gt htb)]
      exact hξ.sphere _ (time_shift ⟨le_of_not_gt htb, ht.2⟩)
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | hbt
    · apply (old_deriv t ⟨ht.1, htb⟩).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htb)]
        with u hu hub using ⟨hu.1, hub⟩
    · subst t
      have hηlim : Tendsto η (𝓝[<] b) (𝓝 (η b)) := by
        rw [new_eq b le_rfl, sub_self, hstart]
        apply hlim.congr'
        filter_upwards [self_mem_nhdsWithin] with u hu using (old_eq u hu).symm
      have hleft := endpoint_left_deriv hab (fun u hu =>
        (old_deriv u (Ioo_subset_Ico_self hu)).hasDerivAt
          (mem_of_superset (Ioo_mem_nhds hu.1 hu.2) Ioo_subset_Ico_self)) hηlim
      have hboth := (hleft.mono (Icc_subset_Iic_self : Icc a b ⊆ Iic b)).union
        (new_deriv b (left_mem_Icc.mpr hbc.le))
      rwa [Icc_union_Icc_eq_Icc hab.le hbc.le] at hboth
    · apply (new_deriv t ⟨hbt.le, ht.2⟩).mono_of_mem_nhdsWithin
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbt)]
        with u hu hbu using ⟨hbu.le, hu.2⟩

end GaussianTesting.TensorSquare
