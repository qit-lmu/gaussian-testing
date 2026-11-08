module

public import GaussianTesting.GradientFlow.Abstract
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Local unit-vector solutions in Lemma 3.1

Local solutions with the same initial value agree on their common time interval.
On each closed subinterval the integral of the squared speed equals the increase
in acceptance probability. These conclusions require only the local ODE.
-/
namespace GaussianTesting.TensorSquare

open Set

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K}

omit [CompleteSpace K] in
private theorem IsUnitFlowOn.deriv_right_of_mem_Ico {γ : ℝ → H} {a b t : ℝ}
    (hγ : T.IsUnitFlowOn P γ (Icc a b)) (ht : t ∈ Ico a b) :
    HasDerivWithinAt γ (T.gradAccA P (γ t)) (Ici t) t := by
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
  exact ((hγ.deriv t ⟨ht.1, ht.2.le⟩).mono hsub).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ht.2)

/-- Two local solutions agree on any common closed interval at whose left
endpoint they agree. This also compares a local solution with a global one. -/
theorem IsUnitFlowOn.eqOn_Icc {s u : Set ℝ} {γ η : ℝ → H}
    (hγ : T.IsUnitFlowOn P γ s) (hη : T.IsUnitFlowOn P η u) (hP : T.IsAcceptance P)
    {a b : ℝ} (hs : Icc a b ⊆ s) (hu : Icc a b ⊆ u) (ha : γ a = η a) :
    EqOn γ η (Icc a b) := by
  obtain ⟨L, hL⟩ := T.lipschitzOnWith_gradAccA hP hP.norm_le_one
  have hball {x : H} (hx : ‖x‖ = 1) : x ∈ Metric.closedBall (0 : H) 2 := by
    simp [Metric.mem_closedBall, dist_zero_right, hx]
  have hγ' := hγ.mono hs
  have hη' := hη.mono hu
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => Metric.closedBall (0 : H) 2)
    (v := fun _ => T.gradAccA P) (K := L)
  · exact fun _ _ => hL
  · exact fun t ht => (hγ'.deriv t ht).continuousWithinAt
  · exact fun _ ht => hγ'.deriv_right_of_mem_Ico ht
  · exact fun t ht => hball (hγ'.sphere t ⟨ht.1, ht.2.le⟩)
  · exact fun t ht => (hη'.deriv t ht).continuousWithinAt
  · exact fun _ ht => hη'.deriv_right_of_mem_Ico ht
  · exact fun t ht => hball (hη'.sphere t ⟨ht.1, ht.2.le⟩)
  · exact ha

/-- Local solutions starting together at `a` and ending at `b` and `c` coincide
on the intersection of their time intervals. -/
theorem IsUnitFlowOn.eqOn_overlap {γ η : ℝ → H} {a b c : ℝ}
    (hγ : T.IsUnitFlowOn P γ (Icc a b)) (hη : T.IsUnitFlowOn P η (Icc a c))
    (hP : T.IsAcceptance P) (ha : γ a = η a) : EqOn γ η (Icc a (min b c)) :=
  hγ.eqOn_Icc hη hP (Icc_subset_Icc_right (min_le_left b c))
    (Icc_subset_Icc_right (min_le_right b c)) ha

/-- The squared speed integrated on a closed subinterval is exactly its
endpoint difference in acceptance probability. -/
theorem IsUnitFlowOn.integral_norm_grad_sq_eq {γ : ℝ → H} {s : Set ℝ}
    (hγ : T.IsUnitFlowOn P γ s) (hP : T.IsAcceptance P)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    (∫ t in a..b, ‖T.gradAccA P (γ t)‖ ^ 2) = T.accProbA P (γ b) - T.accProbA P (γ a) := by
  have hγcont : ContinuousOn γ (Icc a b) := fun t ht =>
    ((hγ.deriv t (hI ht)).mono hI).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · intro t ht
    exact ((hγ.hasDerivWithinAt_accProb hP (hI ht)).mono hI).continuousWithinAt
  · intro t ht
    exact ((hγ.hasDerivWithinAt_accProb hP (hI (mem_Icc_of_Ioo ht))).mono hI).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact (((T.contDiff_gradAccA P).continuous.comp_continuousOn hγcont).norm.pow 2).intervalIntegrable_of_Icc hab

/-- The energy identity of Lemma 3.1 in terms of the velocity of the curve
within the interval of integration. A singleton interval has zero energy. -/
theorem IsUnitFlowOn.integral_norm_velocity_sq_eq {γ : ℝ → H} {s : Set ℝ}
    (hγ : T.IsUnitFlowOn P γ s) (hP : T.IsAcceptance P)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ s) :
    (∫ t in a..b, ‖derivWithin γ (Icc a b) t‖ ^ 2) = T.accProbA P (γ b) - T.accProbA P (γ a) := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · rw [← hγ.integral_norm_grad_sq_eq hP hlt.le hI]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hlt.le]
    intro t ht
    exact congrArg (fun v : H => ‖v‖ ^ 2)
      (((hγ.deriv t (hI ht)).mono hI).derivWithin ((uniqueDiffOn_Icc hlt) t ht))

end GaussianTesting.TensorSquare
