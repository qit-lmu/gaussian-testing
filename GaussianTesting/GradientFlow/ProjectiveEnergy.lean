module

public import GaussianTesting.GradientFlow.FubiniStudy
public import GaussianTesting.GradientFlow.MaximalFlow
public import GaussianTesting.GradientFlow.ProjectiveFlow

@[expose] public section

/-!
# Energy and finite-time limits of projective gradient trajectories

An arbitrary solution of the ODE in ray charts agrees on a closed subinterval
with the projection of the unit-vector solution starting from a representative
of its initial ray. The Fubini–Study energy estimate therefore applies to
the ray curve itself. Completeness supplies its limit at a finite endpoint.
-/

namespace GaussianTesting.TensorSquare

open Set Filter Topology
open scoped InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K} {ρ : ℝ → Projectivization ℂ H}

/-- The acceptance probability of a ray, evaluated on a normalized representative. -/
def rayAcceptance (T : TensorSquare H K) (P : K →L[ℂ] K) (q : Projectivization ℂ H) : ℝ :=
  T.accProbA P (rayUnitRep q)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Any unit representative gives the same acceptance probability. -/
theorem rayAcceptance_mk (T : TensorSquare H K) (P : K →L[ℂ] K)
    (x : H) (hx : ‖x‖ = 1) (hn : x ≠ 0) :
    T.rayAcceptance P (Projectivization.mk ℂ x hn) = T.accProbA P x := by
  obtain ⟨z, hz, hrep⟩ := rayUnitRep_phase x hx hn
  rw [rayAcceptance, hrep, T.accProbA_phase P z hz]

/-- On a closed interval an arbitrary projective solution admits a horizontal
unit lift starting at any prescribed unit representative of its initial ray.
Unit-vector ODE uniqueness determines this lift throughout the interval. -/
theorem IsProjectiveFlowOn.exists_unit_lift_Icc {s : Set ℝ} (hρ : T.IsProjectiveFlowOn P ρ s)
    (hP : T.IsAcceptance P) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s)
    (x : H) (hx : ‖x‖ = 1) (hxray : ∀ hn : x ≠ 0, ρ a = Projectivization.mk ℂ x hn) :
    ∃ γ : ℝ → H, γ a = x ∧ T.IsUnitFlowOn P γ (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ hn : γ t ≠ 0, ρ t = Projectivization.mk ℂ (γ t) hn := by
  classical
  obtain ⟨ξ, hξ₀, hξ⟩ := exists_global_unitFlow_by_continuation hP hx
  let γ (t : ℝ) := ξ (t - a)
  have hshift : MapsTo (fun t : ℝ => t - a) (Icc a b) (Ici 0) :=
    fun _ ht => sub_nonneg.mpr ht.1
  have hγ : T.IsUnitFlowOn P γ (Icc a b) := by
    constructor
    · exact fun t ht => hξ.sphere _ (hshift ht)
    · intro t ht
      have hd := (hξ.deriv (t - a) (hshift ht)).scomp t
        ((hasDerivAt_id t).sub_const a).hasDerivWithinAt hshift
      simpa only [γ, id_eq, one_smul, Function.comp_def] using hd
  let σ (t : ℝ) := if hn : γ t ≠ 0 then Projectivization.mk ℂ (γ t) hn else ρ a
  have hσrep (t : ℝ) (_ : t ∈ Icc a b) (hn : γ t ≠ 0) :
      σ t = Projectivization.mk ℂ (γ t) hn := by simp [σ, hn]
  have hγa : γ a = x := by simpa [γ] using hξ₀
  have hσa : σ a = ρ a := by
    have hn : γ a ≠ 0 := fun he => by simp [← hγa, he] at hx
    rw [hσrep a (left_mem_Icc.mpr hab) hn]
    simpa [hγa] using (hxray (hγa ▸ hn)).symm
  have heq := hρ.eqOn_Icc (hγ.projective hσrep) hI Subset.rfl hσa.symm
  exact ⟨γ, hγa, hγ, fun t ht hn => (heq ht).trans (hσrep t ht hn)⟩

/-- The manuscript's distance-energy bound for any solution in ray charts. -/
theorem IsProjectiveFlowOn.dist_sq_le_energy {s : Set ℝ} (hρ : T.IsProjectiveFlowOn P ρ s)
    (hP : T.IsAcceptance P) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    dist (ρ a) (ρ b) ^ 2 ≤ (b - a) * (T.rayAcceptance P (ρ b) - T.rayAcceptance P (ρ a)) := by
  obtain ⟨γ, _, hγ, hrep⟩ := hρ.exists_unit_lift_Icc hP hab hI (rayUnitRep (ρ a))
    (norm_rayUnitRep (ρ a)) (fun _ => (mk_rayUnitRep (ρ a)).symm)
  have ha := left_mem_Icc.mpr hab
  have hb := right_mem_Icc.mpr hab
  have hna : γ a ≠ 0 := fun h => by simpa [h] using hγ.sphere a ha
  have hnb : γ b ≠ 0 := fun h => by simpa [h] using hγ.sphere b hb
  rw [dist_ray_eq, hrep a ha hna, hrep b hb hnb, rayDist_mk _ _ (hγ.sphere a ha) (hγ.sphere b hb),
    rayAcceptance_mk _ _ _ (hγ.sphere b hb), rayAcceptance_mk _ _ _ (hγ.sphere a ha)]
  exact hγ.angle_sq_le_energy hP hab Subset.rfl

/-- Since acceptance lies in the unit interval, squared distance is at most elapsed time. -/
theorem IsProjectiveFlowOn.dist_sq_le_time_sub {s : Set ℝ} (hρ : T.IsProjectiveFlowOn P ρ s)
    (hP : T.IsAcceptance P) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    dist (ρ a) (ρ b) ^ 2 ≤ b - a := by
  apply (hρ.dist_sq_le_energy hP hab hI).trans
  apply mul_le_of_le_one_right (sub_nonneg.mpr hab)
  unfold rayAcceptance
  linarith [T.accProbA_nonneg hP (rayUnitRep (ρ a)), T.accProbA_le_one hP (norm_rayUnitRep (ρ b))]

/-- A ray solution converges at every finite positive-length right endpoint,
by the distance estimate and completeness in the Fubini–Study metric. -/
theorem IsProjectiveFlowOn.exists_limit_Ico {a b : ℝ}
    (hρ : T.IsProjectiveFlowOn P ρ (Ico a b)) (hP : T.IsAcceptance P) (hab : a < b) :
    ∃ q : Projectivization ℂ H, Tendsto ρ (𝓝[<] b) (𝓝 q) := by
  have hUC : UniformContinuousOn ρ (Ico a b) := by
    apply Metric.uniformContinuousOn_iff.mpr
    intro ε hε
    refine ⟨ε ^ 2, sq_pos_of_pos hε, ?_⟩
    intro x hx y hy hxy
    wlog hle : x ≤ y generalizing x y
    · simpa only [dist_comm (ρ y) (ρ x)] using
        this y hy x hx (by rwa [dist_comm]) (le_of_not_ge hle)
    have hI : Icc x y ⊆ Ico a b := fun _ hz => ⟨hx.1.trans hz.1, hz.2.trans_lt hy.2⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)] at hxy
    nlinarith [hρ.dist_sq_le_time_sub hP hle hI, dist_nonneg (x := ρ x) (y := ρ y)]
  have hc : Cauchy (𝓝[<] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  exact cauchy_map_iff_exists_tendsto.mp (hc.map_of_le hUC (le_principal_iff.mpr
    (mem_of_superset (Ioo_mem_nhdsLT hab) Ioo_subset_Ico_self)))

end
end GaussianTesting.TensorSquare
