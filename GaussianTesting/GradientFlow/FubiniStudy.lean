module

public import GaussianTesting.GradientFlow.ProjectiveSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fubini–Study distance

For unit representatives the distance between rays is the arccosine of their
absolute overlap. Phases can be chosen so that this is the ordinary spherical
angle between the representatives. This formula gives a complete metric when
the Hilbert space is complete.
-/
@[expose] public section

namespace GaussianTesting

open Set Topology Filter InnerProductGeometry
open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A unit vector representing a ray. -/
def rayUnitRep (q : Projectivization ℂ H) : H := rayChartSection q.rep

@[simp] theorem norm_rayUnitRep (q : Projectivization ℂ H) : ‖rayUnitRep q‖ = 1 :=
  norm_rayChartSection _ q.rep_nonzero

theorem rayUnitRep_ne_zero (q : Projectivization ℂ H) : rayUnitRep q ≠ 0 := by
  intro h
  simpa [h] using norm_rayUnitRep q

@[simp] theorem mk_rayUnitRep (q : Projectivization ℂ H) :
    Projectivization.mk ℂ (rayUnitRep q) (rayUnitRep_ne_zero q) = q :=
  (mk_rayChartSection _ q.rep_nonzero).trans q.mk_rep

/-- The chosen normalized representative of the ray of a unit vector changes it only by phase. -/
theorem rayUnitRep_phase (x : H) (hx : ‖x‖ = 1) (hn : x ≠ 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ rayUnitRep (Projectivization.mk ℂ x hn) = a • x := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    (mk_rayUnitRep (Projectivization.mk ℂ x hn))
  refine ⟨a, ?_, ha.symm⟩
  calc
    ‖a‖ = ‖a • x‖ := by rw [norm_smul, hx, mul_one]
    _ = _ := by rw [ha, norm_rayUnitRep]

/-- The Fubini–Study distance on the projective space of pure states. -/
def rayDist (q r : Projectivization ℂ H) : ℝ :=
  Real.arccos ‖inner ℂ (rayUnitRep q) (rayUnitRep r)‖

/-- The distance can be computed with any unit representatives. -/
theorem rayDist_mk (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hnx : x ≠ 0) (hny : y ≠ 0) :
    rayDist (Projectivization.mk ℂ x hnx) (Projectivization.mk ℂ y hny) = Real.arccos ‖inner ℂ x y‖ := by
  obtain ⟨a, ha, he⟩ := rayUnitRep_phase x hx hnx
  obtain ⟨b, hb, hf⟩ := rayUnitRep_phase y hy hny
  simp [rayDist, he, hf, inner_smul_left, inner_smul_right, ha, hb]

theorem rayDist_comm (q r : Projectivization ℂ H) : rayDist q r = rayDist r q := by
  simp only [rayDist, norm_inner_symm (rayUnitRep q)]

@[simp] theorem rayDist_self (q : Projectivization ℂ H) : rayDist q q = 0 := by
  simp [rayDist, inner_self_eq_norm_sq_to_K]

private theorem exists_align_phase (c : ℂ) : ∃ a : ℂ, ‖a‖ = 1 ∧ a * c = (‖c‖ : ℂ) := by
  by_cases hc : c = 0
  · exact ⟨1, norm_one, by simp [hc]⟩
  · refine ⟨(‖c‖ : ℂ) / c, ?_, div_mul_cancel₀ _ hc⟩
    simp [norm_ne_zero_iff.mpr hc]

/-- Fix the representative of one ray. The other has a unit representative for
which the inner product is real and nonnegative. -/
private theorem aligned_rep (x : H) (q : Projectivization ℂ H) :
    ∃ y : H, ∃ hy : y ≠ 0, ‖y‖ = 1 ∧ Projectivization.mk ℂ y hy = q ∧
      inner ℂ x y = (‖inner ℂ x y‖ : ℂ) := by
  obtain ⟨a, ha, hh⟩ := exists_align_phase (inner ℂ x (rayUnitRep q))
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hy0 : a • rayUnitRep q ≠ 0 := smul_ne_zero ha0 (rayUnitRep_ne_zero q)
  refine ⟨a • rayUnitRep q, hy0, by simp [norm_smul, ha], ?_, ?_⟩
  · exact ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, rfl⟩).trans (mk_rayUnitRep q)
  · rw [inner_smul_right, hh]
    simp

private lemma rayDist_le_realAngle (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hnx : x ≠ 0) (hny : y ≠ 0) :
    letI := InnerProductSpace.rclikeToReal ℂ H
    rayDist (Projectivization.mk ℂ x hnx) (Projectivization.mk ℂ y hny) ≤ angle x y := by
  let := InnerProductSpace.rclikeToReal ℂ H
  rw [rayDist_mk _ _ hx hy, angle, hx, hy, one_mul, div_one]
  exact Real.arccos_le_arccos (Complex.re_le_norm _)

private lemma aligned_angle (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : inner ℂ x y = (‖inner ℂ x y‖ : ℂ)) :
    letI := InnerProductSpace.rclikeToReal ℂ H
    angle x y = Real.arccos ‖inner ℂ x y‖ := by
  let := InnerProductSpace.rclikeToReal ℂ H
  rw [angle, hx, hy, one_mul, div_one]
  change Real.arccos (inner ℂ x y).re = _
  exact congrArg Real.arccos (congrArg Complex.re h)

theorem rayDist_triangle (q r s : Projectivization ℂ H) :
    rayDist q s ≤ rayDist q r + rayDist r s := by
  let := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨x, hnx, hx, hqx, halignx⟩ := aligned_rep (rayUnitRep r) q
  obtain ⟨z, hnz, hz, hsz, halignz⟩ := aligned_rep (rayUnitRep r) s
  have hxr : angle x (rayUnitRep r) = rayDist q r := by
    rw [angle_comm, aligned_angle _ _ (norm_rayUnitRep r) hx halignx, rayDist_comm q r, ← hqx,
      ← rayDist_mk _ _ (norm_rayUnitRep r) hx (rayUnitRep_ne_zero r) hnx, mk_rayUnitRep]
  have hrz : angle (rayUnitRep r) z = rayDist r s := by
    rw [aligned_angle _ _ (norm_rayUnitRep r) hz halignz, ← hsz,
      ← rayDist_mk _ _ (norm_rayUnitRep r) hz (rayUnitRep_ne_zero r) hnz, mk_rayUnitRep]
  calc
    rayDist q s ≤ angle x z := hqx ▸ hsz ▸ rayDist_le_realAngle x z hx hz hnx hnz
    _ ≤ angle x (rayUnitRep r) + angle (rayUnitRep r) z := angle_le_angle_add_angle _ _ _
    _ = _ := by rw [hxr, hrz]

/-- One can choose the representative of the second ray so that its chord to
a prescribed unit representative of the first ray is at most their distance. -/
theorem exists_rayRep_dist_le (x : H) (hx : ‖x‖ = 1) (hnx : x ≠ 0) (q : Projectivization ℂ H) :
    ∃ y : H, ∃ hy : y ≠ 0, ‖y‖ = 1 ∧ Projectivization.mk ℂ y hy = q ∧
      dist x y ≤ rayDist (Projectivization.mk ℂ x hnx) q := by
  obtain ⟨y, hny, hy, hqy, hA⟩ := aligned_rep x q
  refine ⟨y, hny, hy, hqy, ?_⟩
  rw [← hqy, rayDist_mk _ _ hx hy, dist_eq_norm]
  have hr : (inner ℂ x y).re = ‖inner ℂ x y‖ := congrArg Complex.re hA
  have hu : ‖inner ℂ x y‖ ≤ 1 := by simpa [hx, hy] using norm_inner_le_norm (𝕜 := ℂ) x y
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ‖inner ℂ x y‖)
  rw [Real.cos_arccos (by linarith [norm_nonneg (inner ℂ x y)]) hu] at hc
  have he := norm_sub_sq (𝕜 := ℂ) x y
  change ‖x-y‖^2 = ‖x‖^2 - 2 * (inner ℂ x y).re + ‖y‖^2 at he
  rw [hx, hy, hr] at he
  nlinarith [norm_nonneg (x-y), Real.arccos_nonneg ‖inner ℂ x y‖]

theorem ray_eq_of_dist_eq_zero (q r : Projectivization ℂ H) (h : rayDist q r = 0) : q = r := by
  obtain ⟨y, hn, _, he, hd⟩ := exists_rayRep_dist_le (rayUnitRep q) (norm_rayUnitRep q)
    (rayUnitRep_ne_zero q) r
  rw [mk_rayUnitRep, h, dist_le_zero] at hd
  subst y
  exact (mk_rayUnitRep q).symm.trans he

private lemma rayDist_mk_nonzero (q : Projectivization ℂ H) (x : {v : H // v ≠ 0}) :
    rayDist q (Projectivization.mk' ℂ x) = Real.arccos ‖inner ℂ (rayUnitRep q) (rayChartSection x)‖ := by
  have hn : rayChartSection (x : H) ≠ 0 := by
    intro h
    simpa [h] using norm_rayChartSection _ x.property
  calc
    _ = rayDist (Projectivization.mk ℂ (rayUnitRep q) (rayUnitRep_ne_zero q))
          (Projectivization.mk ℂ (rayChartSection x) hn) := by rw [mk_rayUnitRep, mk_rayChartSection]; rfl
    _ = _ := rayDist_mk _ _ (norm_rayUnitRep _) (norm_rayChartSection _ x.property) _ _

/-- Distance to a fixed ray is continuous in the quotient topology. -/
theorem continuous_rayDist (q : Projectivization ℂ H) : Continuous (rayDist q) := by
  apply isQuotientMap_rayMk.continuous_iff.mpr
  change Continuous (fun x : {v : H // v ≠ 0} => rayDist q (Projectivization.mk' ℂ x))
  simp_rw [rayDist_mk_nonzero]
  apply Real.continuous_arccos.comp
  apply Continuous.norm
  apply continuous_const.inner
  exact continuous_iff_continuousAt.mpr fun x =>
    (contDiffAt_rayChartSection (x : H) x.property).continuousAt.comp continuous_subtype_val.continuousAt

theorem isOpen_iff_rayDist_ball (S : Set (Projectivization ℂ H)) :
    IsOpen S ↔ ∀ q ∈ S, ∃ ε > 0, ∀ r, rayDist q r < ε → r ∈ S := by
  constructor
  · intro hS q hq
    let x : {v : H // v ≠ 0} := ⟨rayUnitRep q, rayUnitRep_ne_zero q⟩
    have hpre := hS.preimage isQuotientMap_rayMk.continuous
    have hx : x ∈ (Projectivization.mk' ℂ) ⁻¹' S := by simpa [x] using hq
    obtain ⟨ε, he, hball⟩ := Metric.isOpen_iff.mp hpre x hx
    refine ⟨ε, he, fun r hr => ?_⟩
    obtain ⟨y, hy, _, hmk, hd⟩ := exists_rayRep_dist_le (rayUnitRep q) (norm_rayUnitRep q)
      (rayUnitRep_ne_zero q) r
    rw [mk_rayUnitRep] at hd
    have hballmem : (⟨y,hy⟩ : {v : H // v ≠ 0}) ∈ Metric.ball x ε := by
      change dist y (rayUnitRep q) < ε
      exact (dist_comm _ _).trans_le hd |>.trans_lt hr
    simpa [← hmk] using hball hballmem
  · intro h
    apply isOpen_iff_forall_mem_open.mpr
    intro q hq
    obtain ⟨ε, he, hε⟩ := h q hq
    exact ⟨{r | rayDist q r < ε}, fun r hr => hε r hr,
      isOpen_lt (continuous_rayDist q) continuous_const, by simpa using he⟩

/-- The Fubini–Study metric induces the quotient topology of nonzero vectors. -/
instance rayMetricSpace : MetricSpace (Projectivization ℂ H) :=
  MetricSpace.ofDistTopology rayDist rayDist_self rayDist_comm rayDist_triangle
    isOpen_iff_rayDist_ball ray_eq_of_dist_eq_zero

@[simp] theorem dist_ray_eq (q r : Projectivization ℂ H) : dist q r = rayDist q r := rfl

/-- A rapidly Cauchy sequence of rays admits a Cauchy sequence of unit
representatives: choose each new phase relative to the preceding vector. -/
instance rayCompleteSpace [CompleteSpace H] : CompleteSpace (Projectivization ℂ H) := by
  apply Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ)^n) (fun _ => by positivity)
  intro q hq
  let Rep (n : ℕ) := {x : H // ‖x‖ = 1 ∧ ∃ hx : x ≠ 0, Projectivization.mk ℂ x hx = q n}
  have nextRep (n : ℕ) (x : Rep n) :
      ∃ y : Rep (n + 1), dist (x : H) (y : H) ≤ rayDist (q n) (q (n+1)) := by
    obtain ⟨hx, hmk⟩ := x.property.2
    obtain ⟨y, hy, hu, he, hb⟩ := exists_rayRep_dist_le (x : H) x.property.1 hx (q (n+1))
    rw [hmk] at hb
    exact ⟨⟨y,hu,hy,he⟩, hb⟩
  let v : (n : ℕ) → Rep n := Nat.rec
    ⟨rayUnitRep (q 0), norm_rayUnitRep _, rayUnitRep_ne_zero _, mk_rayUnitRep _⟩
    (fun n x => Classical.choose (nextRep n x))
  have hC : CauchySeq (fun n => (v n).val) := by
    apply cauchySeq_of_le_geometric (1/2 : ℝ) 1 (by norm_num)
    intro n
    have hd := (Classical.choose_spec (nextRep n (v n))).trans
      (hq n n (n+1) le_rfl (Nat.le_succ n)).le
    simpa only [one_mul] using hd
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hC
  have hnorm : ‖x‖ = 1 := tendsto_nhds_unique hx.norm
    (by simpa only [(v _).property.1] using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop)))
  have hn : x ≠ 0 := by intro h; simp [h] at hnorm
  refine ⟨Projectivization.mk ℂ x hn, ?_⟩
  let w (n : ℕ) : {y : H // y ≠ 0} := ⟨(v n).val, (v n).property.2.choose⟩
  have hw : Tendsto w atTop (𝓝 (⟨x,hn⟩ : {y : H // y ≠ 0})) := tendsto_subtype_rng.mpr hx
  have hproj := isQuotientMap_rayMk.continuous.continuousAt.tendsto.comp hw
  have hfun : Projectivization.mk' ℂ ∘ w = q :=
    funext fun n => (v n).property.2.choose_spec
  rwa [hfun] at hproj

end
end GaussianTesting
