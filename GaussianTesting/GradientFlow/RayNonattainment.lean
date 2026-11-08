module

public import GaussianTesting.GradientFlow.RayEnergyIdentity

@[expose] public section

/-!
# Acceptance stays below one at finite times

The paragraph after Eq. (3.7) uses the upper bound on the squared gradient
norm to show that the rejection probability decays at most exponentially.
This estimate applies to every forward solution on projective space.
-/

namespace GaussianTesting.TensorSquare

open Set Filter Topology

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K} {ρ : ℝ → Projectivization ℂ H}

/-- The rejection bound after Eq. (3.7), without a spectral hypothesis. -/
theorem IsProjectiveFlowOn.one_sub_rayAcceptance_ge
    (hρ : T.IsProjectiveFlowOn P ρ (Ici 0)) (hP : T.IsAcceptance P)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(16 * t)) * (1 - T.rayAcceptance P (ρ 0)) ≤ 1 - T.rayAcceptance P (ρ t) := by
  let f := fun s => (1 - T.rayAcceptance P (ρ s)) * Real.exp (16 * s)
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivWithinAt f
        ((-T.rayGradientNormSq P (ρ s)) * Real.exp (16 * s) +
          (1 - T.rayAcceptance P (ρ s)) * (Real.exp (16 * s) * 16)) (Ici 0) s := by
    apply ((hρ.hasDerivWithinAt_rayAcceptance hP hs).const_sub 1).mul
    simpa using (((hasDerivAt_id s).const_mul 16).exp.hasDerivWithinAt (s := Ici 0))
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun s hs => (hd s hs).continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).mono interior_subset
    · intro s hs
      have hq := T.qProbA_le_accProbA hP (norm_rayUnitRep (ρ s))
      have hn := T.norm_gradAccA_sq hP (norm_rayUnitRep (ρ s))
      have hb : T.rayGradientNormSq P (ρ s) ≤ 16 * (1 - T.rayAcceptance P (ρ s)) := by
        change ‖T.gradAccA P (rayUnitRep (ρ s))‖ ^ 2 ≤
          16 * (1 - T.accProbA P (rayUnitRep (ρ s)))
        nlinarith [sq_nonneg (1 - T.accProbA P (rayUnitRep (ρ s)))]
      have he := mul_nonneg (Real.exp_pos (16 * s)).le (sub_nonneg.mpr hb)
      nlinarith
  have h := hm (mem_Ici.mpr (le_refl (0 : ℝ))) ht ht
  have he : Real.exp (-(16 * t)) * Real.exp (16 * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(16 * t))).le
  dsimp [f] at hh
  simp only [mul_zero, Real.exp_zero, mul_one] at hh
  have heq : Real.exp (-(16 * t)) * ((1 - T.rayAcceptance P (ρ t)) * Real.exp (16 * t)) =
      1 - T.rayAcceptance P (ρ t) := by
    calc
      _ = (Real.exp (-(16 * t)) * Real.exp (16 * t)) * (1 - T.rayAcceptance P (ρ t)) := by ring
      _ = _ := by rw [he, one_mul]
  rwa [heq] at hh

/-- A forward ray trajectory starting below certainty stays below certainty
at every finite time. -/
theorem IsProjectiveFlowOn.rayAcceptance_lt_one
    (hρ : T.IsProjectiveFlowOn P ρ (Ici 0)) (hP : T.IsAcceptance P)
    (h0 : T.rayAcceptance P (ρ 0) < 1) {t : ℝ} (ht : 0 ≤ t) :
    T.rayAcceptance P (ρ t) < 1 := by
  have hbound := hρ.one_sub_rayAcceptance_ge hP ht
  have hpos := mul_pos (Real.exp_pos (-(16 * t))) (sub_pos.mpr h0)
  linarith

end GaussianTesting.TensorSquare
