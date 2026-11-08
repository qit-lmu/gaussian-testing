module

public import GaussianTesting.GradientFlow.ProjectiveSpace
public import GaussianTesting.GradientFlow.Phase

@[expose] public section

/-!
# The projective gradient flow in affine ray charts

The ODE is imposed on the coordinates of the ray curve itself. Its velocity
in a chart is the derivative of the affine coordinate function applied to the
vector field at a normalized representative. Local Lipschitz uniqueness for
this chart ODE compares arbitrary projective solutions.
-/

namespace GaussianTesting.TensorSquare

open Filter Set Topology
open scoped InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K}

/-- Velocity in the affine coordinates based at `u`, evaluated at the
normalized representative of the ray with coordinates `w`. -/
def chartGrad (T : TensorSquare H K) (P : K →L[ℂ] K) (u w : H) : H :=
  fderiv ℝ (rayAffine u) (rayChartSection w) (T.gradAccA P (rayChartSection w))

/-- The affine-coordinate velocity is smooth where the chart overlap is nonzero. -/
theorem contDiffAt_chartGrad (u w : H) (hw : inner ℂ u w ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (T.chartGrad P u) w := by
  have hw0 : w ≠ 0 := fun h => hw (by simp [h])
  have hs := contDiffAt_rayChartSection w hw0
  have hs' : inner ℂ u (rayChartSection w) ≠ 0 := by
    simp [rayChartSection, inner_smul_right, hw, hw0]
  have ha := contDiffAt_rayAffine u _ hs'
  have hD : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ (rayAffine u)) (rayChartSection w) :=
    ha.fderiv_right (by simp)
  exact (hD.comp w hs).clm_apply ((T.contDiff_gradAccA P).contDiffAt.comp w hs)

/-- A continuous ray curve solves the projective ODE if its coordinates in
every chart through its current ray have the prescribed velocity. -/
structure IsProjectiveFlowOn (T : TensorSquare H K) (P : K →L[ℂ] K)
    (ρ : ℝ → Projectivization ℂ H) (s : Set ℝ) : Prop where
  continuous : ContinuousOn ρ s
  deriv : ∀ t ∈ s, ∀ u : H, ρ t ∈ rayChartDomain u →
    HasDerivWithinAt (fun r => rayChart u (ρ r)) (T.chartGrad P u (rayChart u (ρ t))) s t

omit [CompleteSpace K] in
theorem IsProjectiveFlowOn.mono {ρ : ℝ → Projectivization ℂ H} {s d : Set ℝ}
    (h : T.IsProjectiveFlowOn P ρ s) (hd : d ⊆ s) : T.IsProjectiveFlowOn P ρ d :=
  ⟨h.continuous.mono hd, fun t ht u hu => (h.deriv t (hd ht) u hu).mono hd⟩

omit [CompleteSpace H] in
private theorem fderiv_rayAffine_smul (u x v : H) {z : ℂ} (hz : z ≠ 0)
    (hx : inner ℂ u x ≠ 0) :
    fderiv ℝ (rayAffine u) (z • x) (z • v) = fderiv ℝ (rayAffine u) x v := by
  let M : H →L[ℝ] H := z • ContinuousLinearMap.id ℝ H
  have hz' : inner ℂ u (z • x) ≠ 0 := by simp [inner_smul_right, hz, hx]
  have h := ((contDiffAt_rayAffine u (z • x) hz').differentiableAt (by simp)).hasFDerivAt.comp x
    M.hasFDerivAt
  have hfun : (rayAffine u) ∘ (fun y : H => z • y) = rayAffine u := funext fun y => rayAffine_smul u y hz
  rw [hfun] at h
  exact (congrArg (fun L : H →L[ℝ] H => L v) h.fderiv).symm

/-- Projecting a unit-vector solution to rays solves the chart ODE. The
values of either curve outside its time domain are immaterial. -/
theorem IsUnitFlowOn.projective {γ : ℝ → H} {s : Set ℝ} (hγ : T.IsUnitFlowOn P γ s)
    {ρ : ℝ → Projectivization ℂ H}
    (hρ : ∀ t (_ht : t ∈ s) (hn : γ t ≠ 0), ρ t = Projectivization.mk ℂ (γ t) hn) :
    T.IsProjectiveFlowOn P ρ s := by
  have hn (t : ℝ) (ht : t ∈ s) : γ t ≠ 0 := fun h => by simpa [h] using hγ.sphere t ht
  have hc : ContinuousOn γ s := fun t ht => (hγ.deriv t ht).continuousWithinAt
  constructor
  · rw [continuousOn_iff_continuous_domRestrict]
    let g : s → {v : H // v ≠ 0} := fun t => ⟨γ t, hn t t.property⟩
    have hg : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hc).subtype_mk _
    exact (isQuotientMap_rayMk.continuous.comp hg).congr (fun t => (hρ t t.property _).symm)
  · intro t ht u hu
    have hrep := hρ t ht (hn t ht)
    rw [hrep, mem_rayChartDomain_mk] at hu
    have hvel : T.chartGrad P u (rayChart u (ρ t)) =
        fderiv ℝ (rayAffine u) (γ t) (T.gradAccA P (γ t)) := by
      obtain ⟨z, hz, hzv⟩ := rayChartSection_rayChart_mk u (γ t) (hγ.sphere t ht) (hn t ht) hu
      rw [chartGrad, hrep, hzv, T.gradAccA_phase P z hz]
      exact fderiv_rayAffine_smul _ _ _ (fun h => by simp [h] at hz) hu
    rw [hvel]
    have h := ((contDiffAt_rayAffine u _ hu).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivWithinAt
      t (hγ.deriv t ht)
    exact h.congr (fun r hr => by rw [hρ r hr (hn r hr), rayChart_mk]; rfl)
      (by rw [hrep, rayChart_mk]; rfl)

/-- In every affine chart containing the curve on a closed interval, its
coordinates are smooth, including one-sided derivatives at the endpoints. -/
theorem IsProjectiveFlowOn.contDiffOn_chart {ρ : ℝ → Projectivization ℂ H} {s : Set ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ s) {a b : ℝ} (hs : Icc a b ⊆ s) {u : H}
    (hu : ∀ t ∈ Icc a b, ρ t ∈ rayChartDomain u) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t => rayChart u (ρ t)) (Icc a b) := by
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (f := fun _ x => T.chartGrad P u x)
    (u := {w | inner ℂ u w ≠ 0})
  · intro tx htx
    exact ((contDiffAt_chartGrad u tx.2 htx.2).comp tx contDiffAt_snd).contDiffWithinAt
  · exact fun t ht => (hρ.deriv t (hs ht) u (hu t ht)).mono hs
  · intro t ht
    exact ne_of_eq_of_ne (inner_rayChart u _ (hu t ht)) one_ne_zero

/-- At any time of a half-line solution, each chart containing the current
ray gives smooth coordinates within the half-line. This includes its initial
time and does not require the entire trajectory to stay in one chart. -/
theorem IsProjectiveFlowOn.contDiffWithinAt_chart_Ici {ρ : ℝ → Projectivization ℂ H}
    {a t : ℝ} (hρ : T.IsProjectiveFlowOn P ρ (Ici a)) (ht : t ∈ Ici a)
    {u : H} (hu : ρ t ∈ rayChartDomain u) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun r => rayChart u (ρ r)) (Ici a) t := by
  have hmem : ∀ᶠ r in 𝓝[Ici a] t, ρ r ∈ rayChartDomain u :=
    hρ.continuous t ht ((isOpen_rayChartDomain u).mem_nhds hu)
  obtain ⟨c, d, hcd, hN, hU⟩ := exists_Icc_mem_subset_of_mem_nhds
    (eventually_nhdsWithin_iff.mp hmem)
  have hI : Icc (max a c) d ⊆ Ici a := fun _ hr => (le_max_left a c).trans hr.1
  have hJ : Icc (max a c) d ⊆ Icc c d := Icc_subset_Icc_left (le_max_right a c)
  have hsmall := hρ.contDiffOn_chart hI (fun r hr => hU (hJ hr) (hI hr))
  have hat : t ∈ Icc (max a c) d := ⟨max_le ht hcd.1, hcd.2⟩
  apply (hsmall t hat).mono_of_mem_nhdsWithin
  filter_upwards [mem_nhdsWithin_of_mem_nhds hN, self_mem_nhdsWithin] with r hr hr'
  exact ⟨max_le hr' hr.1, hr.2⟩

omit [CompleteSpace K] in
private theorem IsProjectiveFlowOn.eqOn_chart_interval {ρ σ : ℝ → Projectivization ℂ H}
    {a b : ℝ} (hρ : T.IsProjectiveFlowOn P ρ (Icc a b)) (hσ : T.IsProjectiveFlowOn P σ (Icc a b))
    {u : H} {V : Set H} {L : NNReal} (hL : LipschitzOnWith L (T.chartGrad P u) V)
    (hρV : ∀ t ∈ Icc a b, ρ t ∈ rayChartDomain u ∧ rayChart u (ρ t) ∈ V)
    (hσV : ∀ t ∈ Icc a b, σ t ∈ rayChartDomain u ∧ rayChart u (σ t) ∈ V)
    (ha : ρ a = σ a) : EqOn ρ σ (Icc a b) := by
  have hcharts {c : ℝ → Projectivization ℂ H} (hc : T.IsProjectiveFlowOn P c (Icc a b))
      (hV : ∀ t ∈ Icc a b, c t ∈ rayChartDomain u ∧ rayChart u (c t) ∈ V) :
      ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => rayChart u (c t))
        (T.chartGrad P u (rayChart u (c t))) (Icc a b) t :=
    fun t ht => hc.deriv t ht u (hV t ht).1
  have right {f : ℝ → H} {t : ℝ} (ht : t ∈ Ico a b) {v : H}
      (hd : HasDerivWithinAt f v (Icc a b) t) : HasDerivWithinAt f v (Ici t) t :=
    (hd.mono (Icc_subset_Icc_left ht.1)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ht.2)
  have he : EqOn (fun t => rayChart u (ρ t)) (fun t => rayChart u (σ t)) (Icc a b) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => T.chartGrad P u) (s := fun _ => V)
      (fun _ _ => hL) (fun t ht => (hcharts hρ hρV t ht).continuousWithinAt)
      (fun t ht => right ht (hcharts hρ hρV t ⟨ht.1, ht.2.le⟩))
      (fun t ht => (hρV t ⟨ht.1, ht.2.le⟩).2)
      (fun t ht => (hcharts hσ hσV t ht).continuousWithinAt)
      (fun t ht => right ht (hcharts hσ hσV t ⟨ht.1, ht.2.le⟩))
      (fun t ht => (hσV t ⟨ht.1, ht.2.le⟩).2) (congrArg (rayChart u) ha)
  exact fun t ht => rayChart_inj (hρV t ht).1 (hσV t ht).1 (he ht)

private theorem IsProjectiveFlowOn.eq_right {ρ σ : ℝ → Projectivization ℂ H} {a b t : ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ (Icc a b)) (hσ : T.IsProjectiveFlowOn P σ (Icc a b))
    (ht : t ∈ Ico a b) (he : ρ t = σ t) :
    ∀ᶠ r in 𝓝[≥] t, ρ r = σ r := by
  obtain ⟨u, hρu⟩ := exists_rayChartDomain (ρ t)
  have hσu : σ t ∈ rayChartDomain u := he ▸ hρu
  have htc : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
  have hinterval : Icc a b ∈ 𝓝[≥] t :=
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hle := nhdsWithin_le_of_mem hinterval
  have hsmooth := contDiffAt_chartGrad (T := T) (P := P) u (rayChart u (ρ t))
    (ne_of_eq_of_ne (inner_rayChart _ _ hρu) one_ne_zero)
  have hsmooth₁ : ContDiffAt ℝ 1 (T.chartGrad P u) (rayChart u (ρ t)) := hsmooth.of_le (by simp)
  obtain ⟨L, V, hV, hLip⟩ := hsmooth₁.exists_lipschitzOnWith
  have hlocal {c : ℝ → Projectivization ℂ H} (hc : T.IsProjectiveFlowOn P c (Icc a b))
      (hu : c t ∈ rayChartDomain u) (hVt : V ∈ 𝓝 (rayChart u (c t))) :
      ∀ᶠ r in 𝓝[≥] t, c r ∈ rayChartDomain u ∧ rayChart u (c r) ∈ V := by
    have h₁ : ∀ᶠ r in 𝓝[Icc a b] t, c r ∈ rayChartDomain u :=
      hc.continuous t htc ((isOpen_rayChartDomain u).mem_nhds hu)
    have h₂ : ∀ᶠ r in 𝓝[Icc a b] t, rayChart u (c r) ∈ V :=
      (hc.deriv t htc u hu).continuousWithinAt hVt
    exact (h₁.and h₂).filter_mono hle
  have hg : {r | r ∈ Icc a b ∧ (ρ r ∈ rayChartDomain u ∧ rayChart u (ρ r) ∈ V) ∧
      σ r ∈ rayChartDomain u ∧ rayChart u (σ r) ∈ V} ∈ 𝓝[≥] t := by
    filter_upwards [hinterval, hlocal hρ hρu hV, hlocal hσ hσu (he ▸ hV)] with r hr hf hg
    exact ⟨hr, hf, hg⟩
  obtain ⟨d, htd, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hg
  have hs : Icc t d ⊆ Icc a b := fun r hr => (hsub hr).1
  have hEq := (hρ.mono hs).eqOn_chart_interval (hσ.mono hs) hLip
    (fun r hr => (hsub hr).2.1) (fun r hr => (hsub hr).2.2) he
  exact mem_of_superset (Icc_mem_nhdsGE htd) hEq

/-- Any two chart-defined ray solutions agreeing at the start of a common
closed interval agree throughout it. No horizontal lift of either curve is
assumed. -/
theorem IsProjectiveFlowOn.eqOn_Icc {ρ σ : ℝ → Projectivization ℂ H} {s d : Set ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ s) (hσ : T.IsProjectiveFlowOn P σ d)
    {a b : ℝ} (hs : Icc a b ⊆ s) (hd : Icc a b ⊆ d) (ha : ρ a = σ a) :
    EqOn ρ σ (Icc a b) := by
  have hf := hρ.mono hs
  have hg := hσ.mono hd
  let E : Set ℝ := {t | ρ t = σ t}
  have hclosed : IsClosed (E ∩ Icc a b) := by
    rw [isClosed_iff_frequently]
    intro t ht
    have hit := isClosed_iff_frequently.mp (@isClosed_Icc ℝ _ _ _ a b) t (ht.mono fun _ h => h.2)
    have heq : ∃ᶠ r in 𝓝[Icc a b] t, ρ r = σ r := frequently_nhdsWithin_iff.mpr ht
    exact ⟨tendsto_nhds_unique_of_frequently_eq (hf.continuous t hit) (hg.continuous t hit) heq, hit⟩
  apply hclosed.Icc_subset_of_forall_mem_nhdsWithin ha
  intro t ht
  exact (hf.eq_right hg ht.2 ht.1).filter_mono (nhdsWithin_mono t Ioi_subset_Ici_self)

end
end GaussianTesting.TensorSquare
