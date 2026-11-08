module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Topology.UnitInterval

/-!
# The projective angle and the length of a curve of unit vectors

In the proof of Theorem 3.4 the projective angle between two states is bounded by
the length of the gradient trajectory. It suffices to majorize each chord of the
trajectory by the decrease of a real function along the same subinterval.
-/

@[expose] public section

namespace GaussianTesting

open Set Filter InnerProductGeometry
open scoped Topology

private lemma angle_eq_two_arcsin_half_chord {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y = 2 * Real.arcsin (‖x - y‖ / 2) := by
  have hn := angle_nonneg x y
  have hp := angle_le_pi x y
  have hs : 0 ≤ Real.sin (angle x y / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hc := norm_sub_pow_two_real x y
  rw [hx, hy, inner_eq_cos_angle_of_norm_eq_one hx hy] at hc
  have hsin := Real.cos_two_mul (angle x y / 2)
  rw [show 2 * (angle x y / 2) = angle x y by ring] at hsin
  have hchord : Real.sin (angle x y / 2) = ‖x - y‖ / 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (angle x y / 2), norm_nonneg (x - y)]
  rw [← hchord, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)]
  ring

/-- At small chord lengths, the angle is at most any prescribed factor
strictly larger than one times the chord. -/
private lemma exists_angle_le_mul_chord {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {k : ℝ} (hk : 1 < k) :
    ∃ r > 0, ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖x - y‖ < r →
      angle x y ≤ k * ‖x - y‖ := by
  have hd : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
  have he := (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)).eventually_lt_const hk
  obtain ⟨r, hr, hb⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp he
  refine ⟨2 * r, by positivity, fun x y hx hy hxy => ?_⟩
  rw [angle_eq_two_arcsin_half_chord hx hy]
  rcases (norm_nonneg (x - y)).eq_or_lt with hzero | hpos
  · simp [← hzero]
  have h := hb (show ‖x - y‖ / 2 ∈ Ioo 0 r from ⟨by positivity, by linarith⟩)
  simp only [slope_def_field, Real.arcsin_zero, sub_zero] at h
  have hlinear := (div_lt_iff₀ (by positivity : 0 < ‖x - y‖ / 2)).mp h
  linarith

/-- If the decrease of `v` bounds every chord of a continuous unit-vector curve,
it bounds the projective angle of its endpoints (Theorem 3.4, path-length estimate). -/
theorem projective_angle_le_of_chord_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {γ : ℝ → E} {v : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hγ : ContinuousOn γ (Icc 0 t)) (hunit : ∀ s ∈ Icc 0 t, ‖γ s‖ = 1)
    (hchord : ∀ s ∈ Icc 0 t, ∀ u ∈ Icc 0 t, s ≤ u → ‖γ s - γ u‖ ≤ v s - v u) :
    Real.arccos ‖inner ℂ (γ 0) (γ t)‖ ≤ v 0 - v t := by
  let := InnerProductSpace.rclikeToReal ℂ E
  have hzero := left_mem_Icc.mpr ht
  have htmem := right_mem_Icc.mpr ht
  have hproject : Real.arccos ‖inner ℂ (γ 0) (γ t)‖ ≤ angle (γ 0) (γ t) := by
    rw [angle, hunit 0 hzero, hunit t htmem, one_mul, div_one]
    apply Real.arccos_le_arccos
    exact Complex.re_le_norm _
  apply hproject.trans
  -- On a sufficiently fine partition, sum the small angles by the triangle inequality.
  have approximation (k : ℝ) (hk : 1 < k) : angle (γ 0) (γ t) ≤ k * (v 0 - v t) := by
    obtain ⟨r, hr, hlocal⟩ := exists_angle_le_mul_chord (E := E) hk
    -- Intervals in one member of this cover have endpoint chords shorter than r.
    let cover (i : Icc 0 t) : Set (Icc 0 t) := {s | dist (γ s) (γ i) < r / 2}
    have hopen (i) : IsOpen (cover i) :=
      isOpen_lt ((continuousOn_iff_continuous_domRestrict.mp hγ).dist continuous_const) continuous_const
    have hcover : univ ⊆ ⋃ i, cover i := by
      intro s _
      exact mem_iUnion.mpr ⟨s, by simp [cover, hr]⟩
    obtain ⟨p, hp0, hmono, ⟨N, hN⟩, hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_Icc ht hopen hcover
    have partial_bound (n : ℕ) : angle (γ 0) (γ (p n)) ≤ k * (v 0 - v (p n)) := by
      induction n with
      | zero =>
        rw [hp0, sub_self, mul_zero, angle_self]
        intro h
        simpa [h] using hunit 0 hzero
      | succ n ih =>
        obtain ⟨i, hi⟩ := hsub n
        have hle := hmono (Nat.le_succ n)
        have hleft : dist (γ (p n)) (γ i) < r / 2 := hi (left_mem_Icc.mpr hle)
        have hright : dist (γ (p (n + 1))) (γ i) < r / 2 := hi (right_mem_Icc.mpr hle)
        have hsmall : ‖γ (p n) - γ (p (n + 1))‖ < r := by
          rw [← dist_eq_norm]
          linarith [dist_triangle_right (γ (p n)) (γ (p (n + 1))) (γ i)]
        have hab := (hlocal _ _ (hunit _ (p n).property) (hunit _ (p (n + 1)).property)
          hsmall).trans (mul_le_mul_of_nonneg_left
            (hchord _ (p n).property _ (p (n + 1)).property hle) (by positivity))
        exact (angle_le_angle_add_angle _ (γ (p n)) _).trans (by linarith)
    simpa [hN N le_rfl] using partial_bound N
  have lim : Tendsto (fun k : ℝ => k * (v 0 - v t)) (𝓝[>] 1) (𝓝 (v 0 - v t)) := by
    simpa [ContinuousWithinAt] using (continuous_id.mul_const (v 0 - v t)).continuousWithinAt
      (x := (1 : ℝ)) (s := Ioi 1)
  exact ge_of_tendsto lim (mem_of_superset self_mem_nhdsWithin fun k hk => approximation k hk)

end GaussianTesting
