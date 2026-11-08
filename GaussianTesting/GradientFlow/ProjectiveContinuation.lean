module

public import GaussianTesting.GradientFlow.ProjectiveFlow
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-!
# Restart at a finite endpoint of the projective gradient flow

A local solution is constructed on rays by projecting a unit-vector solution.
For any chart-defined trajectory approaching a limiting ray, continuity of the
chart velocity gives the left derivative at the endpoint. A local solution
started at that ray then completes the extension.
-/

namespace GaussianTesting.TensorSquare

open Filter Set Topology
open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K}

/-- Local existence on rays from any prescribed initial ray and time. -/
theorem exists_local_projectiveFlow (hP : T.IsAcceptance P) (b : ℝ) (q : Projectivization ℂ H) :
    ∃ c > b, ∃ ξ : ℝ → Projectivization ℂ H, ξ b = q ∧ T.IsProjectiveFlowOn P ξ (Icc b c) := by
  classical
  let x := rayChartSection q.rep
  have hx : ‖x‖ = 1 := norm_rayChartSection _ q.rep_nonzero
  obtain ⟨δ, hδ, hlocal⟩ := T.exists_smooth_local_unitFlow hP
  obtain ⟨γ, hγ0, hγ, _⟩ := hlocal x hx
  let v (t : ℝ) := γ (t - b)
  have hshift : MapsTo (fun t : ℝ => t - b) (Icc b (b + δ)) (Icc 0 δ) :=
    fun t ht => ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩
  have hv : T.IsUnitFlowOn P v (Icc b (b + δ)) := by
    refine ⟨fun t ht => hγ.sphere _ (hshift ht), ?_⟩
    intro t ht
    have hd := (hγ.deriv _ (hshift ht)).scomp t
      ((hasDerivAt_id t).sub_const b).hasDerivWithinAt hshift
    simpa only [v, one_smul, Function.comp_def, id_eq] using hd
  let ξ (t : ℝ) := if h : v t ≠ 0 then Projectivization.mk ℂ (v t) h else q
  have hrep (t : ℝ) (_ : t ∈ Icc b (b + δ)) (hn : v t ≠ 0) :
      ξ t = Projectivization.mk ℂ (v t) hn := by simp [ξ, hn]
  refine ⟨b + δ, lt_add_of_pos_right _ hδ, ξ, ?_, hv.projective hrep⟩
  have hv0 : v b = x := by simp [v, hγ0]
  have hn : v b ≠ 0 := by intro hz; simp [← hv0, hz] at hx
  rw [hrep b (left_mem_Icc.mpr (by linarith)) hn]
  simpa [hv0, x] using (mk_rayChartSection q.rep q.rep_nonzero).trans q.mk_rep

omit [CompleteSpace K] in
private theorem IsProjectiveFlowOn.congr {ρ η : ℝ → Projectivization ℂ H} {s : Set ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ s) (heq : EqOn η ρ s) : T.IsProjectiveFlowOn P η s := by
  refine ⟨hρ.continuous.congr heq, ?_⟩
  intro t ht u hu
  rw [heq ht] at hu ⊢
  exact (hρ.deriv t ht u hu).congr_of_mem (fun r hr => congrArg (rayChart u) (heq hr)) ht

/-- At the limiting ray, the coordinates of the trajectory have the left
derivative prescribed by the chart equation. Only a final neighborhood of
the trajectory needs to lie in the selected chart. -/
private theorem IsProjectiveFlowOn.chart_deriv_at_endpoint {a b : ℝ} {η : ℝ → Projectivization ℂ H}
    (hη : T.IsProjectiveFlowOn P η (Ico a b)) (hab : a < b)
    (hlim : Tendsto η (𝓝[<] b) (𝓝 (η b))) {u : H} (hu : η b ∈ rayChartDomain u) :
    HasDerivWithinAt (fun r => rayChart u (η r)) (T.chartGrad P u (rayChart u (η b))) (Iic b) b := by
  let W (t : ℝ) := rayChart u (η t)
  let J := {t | t ∈ Ioo a b ∧ η t ∈ rayChartDomain u}
  have hJ : J ∈ 𝓝[<] b :=
    inter_mem (Ioo_mem_nhdsLT hab) (hlim ((isOpen_rayChartDomain u).mem_nhds hu))
  have hW : Tendsto W (𝓝[<] b) (𝓝 (W b)) :=
    ((continuousOn_rayChart u _ hu).continuousAt ((isOpen_rayChartDomain u).mem_nhds hu)).tendsto.comp hlim
  have hd (t : ℝ) (ht : t ∈ J) : HasDerivAt W (T.chartGrad P u (W t)) t :=
    (hη.deriv t (Ioo_subset_Ico_self ht.1) u ht.2).hasDerivAt
      (mem_of_superset (Ioo_mem_nhds ht.1.1 ht.1.2) Ioo_subset_Ico_self)
  have hvel := (contDiffAt_chartGrad (T := T) (P := P) u (W b)
    ((inner_rayChart _ _ hu).trans_ne one_ne_zero)).continuousAt
  apply hasDerivWithinAt_Iic_of_tendsto_deriv (s := J)
  · exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  · exact hW.mono_left (nhdsWithin_mono b (fun t ht => ht.1.2 : J ⊆ Iio b))
  · exact hJ
  · apply (hvel.tendsto.comp hW).congr'
    filter_upwards [hJ] with t ht using (hd t ht).deriv.symm

/-- A chart-defined projective solution with a left limit at a finite endpoint
extends past the endpoint, takes the specified limiting value there, and obeys
the ODE also at the joining time. -/
theorem IsProjectiveFlowOn.exists_extension_of_limit_Ico {a b : ℝ} {ρ : ℝ → Projectivization ℂ H}
    (hρ : T.IsProjectiveFlowOn P ρ (Ico a b)) (hP : T.IsAcceptance P) (hab : a < b)
    {q : Projectivization ℂ H} (hlim : Tendsto ρ (𝓝[<] b) (𝓝 q)) :
    ∃ c > b, ∃ η : ℝ → Projectivization ℂ H,
      EqOn ρ η (Ico a b) ∧ η b = q ∧ T.IsProjectiveFlowOn P η (Icc a c) := by
  obtain ⟨c, hbc, ξ, hξb, hξ⟩ := exists_local_projectiveFlow hP b q
  let η (t : ℝ) := if t < b then ρ t else ξ t
  have old_eq (t : ℝ) (ht : t < b) : η t = ρ t := by simp [η, ht]
  have new_eq (t : ℝ) (ht : b ≤ t) : η t = ξ t := by simp [η, not_lt.mpr ht]
  have hb : η b = q := (new_eq b le_rfl).trans hξb
  have hηlim : Tendsto η (𝓝[<] b) (𝓝 (η b)) := by
    rw [hb]
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht using (old_eq t ht).symm
  have hleft := hρ.congr (fun t ht => old_eq t ht.2)
  have hright := hξ.congr (fun t ht => new_eq t ht.1)
  have hL {t : ℝ} (ht : t < b) : Ico a b ∈ 𝓝[Icc a c] t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)]
      with r hr hrb using ⟨hr.1, hrb⟩
  have hR {t : ℝ} (ht : b < t) : Icc b c ∈ 𝓝[Icc a c] t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)]
      with r hr hbr using ⟨hbr.le, hr.2⟩
  refine ⟨c, hbc, η, fun t ht => (old_eq t ht.2).symm, hb, ?_⟩
  constructor
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | hbt
    · exact (hleft.continuous t ⟨ht.1, htb⟩).mono_of_mem_nhdsWithin (hL htb)
    · subst t
      have hcleft := (continuousWithinAt_Iio_iff_Iic.mp hηlim).mono (Icc_subset_Iic_self : Icc a b ⊆ Iic b)
      have hc := hcleft.union (hright.continuous b (left_mem_Icc.mpr hbc.le))
      rwa [Icc_union_Icc_eq_Icc hab.le hbc.le] at hc
    · exact (hright.continuous t ⟨hbt.le, ht.2⟩).mono_of_mem_nhdsWithin (hR hbt)
  · intro t ht u hu
    rcases lt_trichotomy t b with htb | heq | hbt
    · exact (hleft.deriv t ⟨ht.1, htb⟩ u hu).mono_of_mem_nhdsWithin (hL htb)
    · subst t
      have hd := (hleft.chart_deriv_at_endpoint hab hηlim hu).mono (Icc_subset_Iic_self : Icc a b ⊆ Iic b)
      have hboth := hd.union (hright.deriv b (left_mem_Icc.mpr hbc.le) u hu)
      rwa [Icc_union_Icc_eq_Icc hab.le hbc.le] at hboth
    · exact (hright.deriv t ⟨hbt.le, ht.2⟩ u hu).mono_of_mem_nhdsWithin (hR hbt)

end GaussianTesting.TensorSquare
