module

/-
The existence part of Lemma 3.1 (`lem:ode`) and finite-dimensional gradient-flow estimates
for the angular and linear fidelity bounds of Theorem 3.4.

Properties of the flow:
* We work on the ambient Hilbert space; the unit sphere is invariant for the vector
  field `gradAcc` (its radial component is `4p(1-‖ψ‖²)`, see `re_inner_gradAcc`).
* A uniform time step `δ > 0` works for every initial point on the sphere.
  `exists_global_flow` joins the resulting local Picard–Lindelöf solutions by recursion. Smoothness and uniqueness of the solution are not exported.
* For each unit vector `u`, the function `t ↦ Re⟪u, γ t⟫ + V(p(γ t))` is
  nonincreasing, where `V(p) = arcsin(√((1-p)/(1-c)))/2` is the paper's
  antiderivative (`c = 3α/2`). Taking the supremum over `u` gives the chord bound
  `‖γ t - γ s‖ ≤ V(p_s) - V(p_t)` with the paper's exact constants.
  Summing over partitions bounds the path length by the same potential drop.
  `flow_angle_bound` applies this comparison to the projective angle.
  `angular_witness_of_gap` passes to the flow limit to obtain the sharp angular bound.
* `1 - p_t ≥ e^{-16t}(1 - p_0) > 0` (so `V` stays differentiable) uses `q ≤ p`
  (`qProb_le_accProb`), as in the paper.
-/
public import GaussianTesting.GradientFlow.Calculus
public import GaussianTesting.GradientFlow.Angle
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace
open Set

noncomputable section

variable {ι : Type*} [Fintype ι] {P : H2 ι →ₗ[ℂ] H2 ι}

/-! ### A. Local segments with a uniform step -/

/-- A flow segment of length `δ` starting at `x₀`: solves the ODE on `[0, δ]` and stays
on the unit sphere. -/
structure IsFlowSeg (P : H2 ι →ₗ[ℂ] H2 ι) (δ : ℝ) (x₀ : H ι) (γ : ℝ → H ι) : Prop where
  init : γ 0 = x₀
  deriv : ∀ t ∈ Icc (0 : ℝ) δ, HasDerivWithinAt γ (gradAcc P (γ t)) (Icc 0 δ) t
  sphere : ∀ t ∈ Icc (0 : ℝ) δ, ‖γ t‖ = 1

/-- Uniform-step local existence: there is a single `δ > 0` (depending only on `P`)
such that from every initial point on the unit sphere the flow exists on `[0, δ]` and
stays on the sphere. (Picard–Lindelöf with the Lipschitz data of
`lipschitzOnWith_gradAcc`/`norm_gradAcc_le` on `closedBall 0 2`, plus sphere invariance
via a Grönwall estimate for `‖γ t‖² - 1`, whose derivative is `8p(γ)(1 - ‖γ‖²)` by
`re_inner_gradAcc`.) -/
theorem exists_flowSeg (hP : IsAcceptanceProjection P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ : H ι, ‖x₀‖ = 1 → ∃ γ, IsFlowSeg P δ x₀ γ := by
  obtain ⟨K, hK⟩ := lipschitzOnWith_gradAcc (P := P)
  obtain ⟨M, hM0, hM⟩ := norm_gradAcc_le (P := P)
  let δ : ℝ := 1 / M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀
  have hball : Metric.closedBall x₀ 1 ⊆ Metric.closedBall (0 : H ι) 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx ⊢
    have hh := norm_add_le (x - x₀) x₀
    simp only [sub_add_cancel, sub_zero, hx₀] at hh ⊢
    linarith
  have hpl : IsPicardLindelof (fun _ x => gradAcc P x)
      (⟨0, by exact ⟨le_rfl, hδ.le⟩⟩ : Icc (0 : ℝ) δ) x₀ 1 0 ⟨M, hM0.le⟩ K := by
    constructor
    · exact fun _ _ => hK.mono hball
    · exact fun _ _ => continuousOn_const
    · exact fun _ _ x hx => hM x (hball hx)
    · change M * max (δ - 0) (0 - 0) ≤ (1 : ℝ) - 0
      simp only [sub_zero, sub_self, max_eq_left hδ.le]
      dsimp [δ]
      rw [mul_one_div_cancel hM0.ne']
  obtain ⟨γ, hγ0, hγd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hcont : ContinuousOn γ (Icc 0 δ) := fun t ht => (hγd t ht).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((contDiff_accProb (P := P)).continuous.comp_continuousOn hcont)
  let e : ℝ → ℝ := fun t => ‖γ t‖ ^ 2 - 1
  have he (t : ℝ) (ht : t ∈ Icc 0 δ) :
      HasDerivWithinAt e (-(8 * accProb P (γ t)) * e t) (Icc 0 δ) t := by
    have hi := (hγd t ht).inner ℂ (hγd t ht)
    have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hi
    have hd := hr.sub_const 1
    have hfun : (fun s => (⟪γ s, γ s⟫_ℂ).re - 1) = e := by
      funext s
      exact congrArg (fun x : ℝ => x - 1) (inner_self_eq_norm_sq (𝕜 := ℂ) (γ s))
    change HasDerivWithinAt (fun s => (⟪γ s, γ s⟫_ℂ).re - 1)
      ((⟪γ t, gradAcc P (γ t)⟫_ℂ + ⟪gradAcc P (γ t), γ t⟫_ℂ).re) _ t at hd
    rw [hfun] at hd
    convert hd using 1
    simp only [Complex.add_re]
    rw [show (⟪gradAcc P (γ t), γ t⟫_ℂ).re =
      (⟪γ t, gradAcc P (γ t)⟫_ℂ).re from inner_re_symm (𝕜 := ℂ) _ _,
      re_inner_gradAcc hP]
    dsimp [e]; ring
  have he0 : e 0 = 0 := by simp [e, hγ0, hx₀]
  have hezero : ∀ t ∈ Icc 0 δ, e t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (fun t ht => (he t ht).continuousWithinAt)
      (f' := fun t => -(8 * accProb P (γ t)) * e t) (K := 8 * C) ?_ he0 ?_
    · intro t ht
      exact ((he t ⟨ht.1, ht.2.le⟩).mono
        (show Icc t δ ⊆ Icc 0 δ from fun s hs => ⟨ht.1.trans hs.1, hs.2⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE ht.2)
    · intro t ht
      have hb := hC t ⟨ht.1, ht.2.le⟩
      simp only [Real.norm_eq_abs] at hb ⊢
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num))
        (abs_nonneg _)
  refine ⟨γ, hγ0, hγd, ?_⟩
  intro t ht
  have hz := hezero t ht
  dsimp [e] at hz
  nlinarith [norm_nonneg (γ t)]

/-! ### B. The global flow -/

/-- Global flow on `[0, ∞)`: obtained by gluing segments from `exists_flowSeg`
(recursion over `ℕ`; junction derivatives via `HasDerivWithinAt.union` on
`Icc ∪ Icc = Icc`). -/
theorem exists_global_flow (hP : IsAcceptanceProjection P) {x₀ : H ι} (hx₀ : ‖x₀‖ = 1) :
    ∃ γ : ℝ → H ι, γ 0 = x₀ ∧ (∀ t ∈ Ici (0 : ℝ), ‖γ t‖ = 1) ∧
      ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt γ (gradAcc P (γ t)) (Ici 0) t := by
  classical
  obtain ⟨δ, hδ, hseg⟩ := exists_flowSeg hP
  let X : ℕ → {x : H ι // ‖x‖ = 1} := Nat.rec ⟨x₀, hx₀⟩
    (fun _ x => ⟨Classical.choose (hseg x.1 x.2) δ,
      (Classical.choose_spec (hseg x.1 x.2)).sphere δ ⟨hδ.le, le_rfl⟩⟩)
  let c : ℕ → ℝ → H ι := fun n => Classical.choose (hseg (X n).1 (X n).2)
  have hc (n : ℕ) : IsFlowSeg P δ (X n).1 (c n) := Classical.choose_spec _
  have hnext (n : ℕ) : (X (n + 1)).1 = c n δ := rfl
  let γ : ℝ → H ι := fun t => c ⌊t / δ⌋₊ (t - (⌊t / δ⌋₊ : ℝ) * δ)
  have hfloor (n : ℕ) (t : ℝ) (hl : (n : ℝ) * δ ≤ t)
      (hr : t < ((n : ℝ) + 1) * δ) : ⌊t / δ⌋₊ = n := by
    apply (Nat.floor_eq_iff (div_nonneg (le_trans (by positivity : 0 ≤ (n : ℝ) * δ) hl) hδ.le)).mpr
    exact ⟨(le_div_iff₀ hδ).mpr hl, (div_lt_iff₀ hδ).mpr hr⟩
  have hcoh (n : ℕ) (t : ℝ) (ht : t ∈ Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) :
      γ t = c n (t - (n : ℝ) * δ) := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · simp [γ, hfloor n t ht.1 hlt]
    · have hf : ⌊t / δ⌋₊ = n + 1 := by
        rw [heq, mul_div_cancel_right₀ _ hδ.ne']
        simpa using (Nat.floor_natCast (n + 1) : ⌊((n + 1 : ℕ) : ℝ)⌋₊ = n + 1)
      rw [show γ t = c (n + 1) 0 by
        dsimp [γ]
        rw [hf]
        simp [heq, Nat.cast_add, Nat.cast_one]]
      rw [(hc (n + 1)).init, hnext]
      congr 1
      linarith
  have hbounds (t : ℝ) (ht : 0 ≤ t) :
      (⌊t / δ⌋₊ : ℝ) * δ ≤ t ∧ t < ((⌊t / δ⌋₊ : ℝ) + 1) * δ :=
    ⟨(le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg ht hδ.le)),
      (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (t / δ))⟩
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) :
      HasDerivWithinAt γ (gradAcc P (γ t))
        (Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) t := by
    have hm : MapsTo (fun s : ℝ => s - (n : ℝ) * δ)
        (Icc ((n : ℝ) * δ) (((n : ℝ) + 1) * δ)) (Icc 0 δ) := by
      intro s hs; constructor <;> linarith [hs.1, hs.2]
    have hh := ((hc n).deriv _ (hm ht)).scomp t
      ((hasDerivWithinAt_id t _).sub_const ((n : ℝ) * δ)) hm
    simp only [one_smul, Function.comp_def] at hh
    rw [← hcoh n t ht] at hh
    exact hh.congr (fun s hs => hcoh n s hs) (hcoh n t ht)
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [show γ 0 = c 0 0 by simp [γ]]
    exact (hc 0).init
  · intro t ht
    have hb := hbounds t ht
    rw [hcoh _ t ⟨hb.1, hb.2.le⟩]
    apply (hc _).sphere
    constructor <;> linarith [hb.1, hb.2]
  · intro t ht
    let n := ⌊t / δ⌋₊
    have hb : (n : ℝ) * δ ≤ t ∧ t < ((n : ℝ) + 1) * δ := hbounds t ht
    have hdright := hd n t ⟨hb.1, hb.2.le⟩
    rcases eq_or_lt_of_le hb.1 with heq | hlt
    · cases hn : n with
      | zero =>
        have ht0 : t = 0 := by simpa [hn] using heq.symm
        rw [hn, ht0] at hdright
        rw [ht0]
        exact hdright.mono_of_mem_nhdsWithin (by simpa using Icc_mem_nhdsGE hδ)
      | succ m =>
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by simp
        rw [hn, hcast] at heq hdright hb
        have hdleft := hd m t (by constructor <;> nlinarith [hδ])
        have hu := hdleft.union hdright
        rw [Icc_union_Icc_eq_Icc (by nlinarith [hδ] : (m : ℝ) * δ ≤ ((m : ℝ) + 1) * δ)
          (by nlinarith [hδ] : ((m : ℝ) + 1) * δ ≤ ((m : ℝ) + 1 + 1) * δ)] at hu
        exact hu.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
          (Icc_mem_nhds (by nlinarith [hδ]) (by nlinarith [hδ])))
    · exact hdright.mono_of_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hlt hb.2))

/-! ### C. Properties along the flow

Throughout, `γ` is a global flow as produced by `exists_global_flow` and
`pγ t := accProb P (γ t)`. -/

variable {γ : ℝ → H ι}

/-- Bundle of the global-flow properties. -/
structure IsGlobalFlow (P : H2 ι →ₗ[ℂ] H2 ι) (γ : ℝ → H ι) : Prop where
  sphere : ∀ t ∈ Ici (0 : ℝ), ‖γ t‖ = 1
  deriv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt γ (gradAcc P (γ t)) (Ici 0) t

/-- `p` is differentiable along the flow with derivative `‖gradAcc‖²` (chain rule +
`deriv_accProb_gradAcc`). -/
theorem flow_hasDerivAt_p (hP : IsAcceptanceProjection P) (hγ : IsGlobalFlow P γ)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    HasDerivWithinAt (fun s => accProb P (γ s)) (‖gradAcc P (γ t)‖ ^ 2) (Ici 0) t := by
  have h := (hasFDerivAt_accProb hP (γ t)).comp_hasDerivWithinAt t (hγ.deriv t ht)
  convert h using 1
  · rfl
  · exact (deriv_accProb_gradAcc hP (hγ.sphere t ht)).symm

/-- `p` is nondecreasing along the flow. -/
theorem flow_p_mono (hP : IsAcceptanceProjection P) (hγ : IsGlobalFlow P γ) :
    MonotoneOn (fun t => accProb P (γ t)) (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · exact fun t ht => (flow_hasDerivAt_p hP hγ ht).continuousWithinAt
  · intro t ht
    exact (flow_hasDerivAt_p hP hγ (interior_subset ht)).mono interior_subset
  · intro t ht
    positivity

/-- `1 - p_t ≥ e^{-16 t} (1 - p_0)`: the flow never reaches `p = 1` in finite time
(uses `ṗ = 16(q - p²) ≤ 16(1 - p)` via `qProb_le_accProb` and `accProb_le_one`). -/
theorem flow_one_sub_p_ge (hP : IsAcceptanceProjection P) (hγ : IsGlobalFlow P γ)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    Real.exp (-(16 * t)) * (1 - accProb P (γ 0)) ≤ 1 - accProb P (γ t) := by
  let f := fun s => (1 - accProb P (γ s)) * Real.exp (16 * s)
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivWithinAt f
        ((-‖gradAcc P (γ s)‖ ^ 2) * Real.exp (16 * s) +
          (1 - accProb P (γ s)) * (Real.exp (16 * s) * 16)) (Ici 0) s := by
    apply ((flow_hasDerivAt_p hP hγ hs).const_sub 1).mul
    simpa using (((hasDerivAt_id s).const_mul 16).exp.hasDerivWithinAt (s := Ici 0))
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun s hs => (hd s hs).continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).mono interior_subset
    · intro s hs
      have hu := hγ.sphere s (interior_subset hs)
      have hq := qProb_le_accProb hP hu
      have hp := accProb_le_one hP hu
      have hn := norm_gradAcc_sq hP hu
      have hb : ‖gradAcc P (γ s)‖ ^ 2 ≤ 16 * (1 - accProb P (γ s)) := by
        nlinarith [sq_nonneg (1 - accProb P (γ s))]
      have he := mul_nonneg (Real.exp_pos (16 * s)).le (sub_nonneg.mpr hb)
      nlinarith
  have h := hm (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) ht ht
  have he : Real.exp (-(16 * t)) * Real.exp (16 * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(16 * t))).le
  dsimp [f] at hh
  simp only [mul_zero, Real.exp_zero, mul_one] at hh
  have heq : Real.exp (-(16 * t)) * ((1 - accProb P (γ t)) * Real.exp (16 * t)) =
      1 - accProb P (γ t) := by
    calc
      _ = (Real.exp (-(16 * t)) * Real.exp (16 * t)) * (1 - accProb P (γ t)) := by ring
      _ = _ := by rw [he, one_mul]
  rwa [heq] at hh

/-- Under the spectral gap hypothesis, if `p_0 > 3α/2` then `p_t → 1` along the flow.
(If not, `p_t ≤ 1 - η` for some `η > 0` and all `t`, whence
`ṗ ≥ 16(p_0 - 3α/2)η > 0` uniformly, contradicting `p ≤ 1`.) -/
theorem flow_p_tendsto_one (hP : IsAcceptanceProjection P) {α : ℝ}
    (hgap : SpectralGapHyp P α) (hγ : IsGlobalFlow P γ)
    (h0 : 3 / 2 * α < accProb P (γ 0)) :
    Filter.Tendsto (fun n : ℕ => accProb P (γ n)) Filter.atTop (nhds 1) := by
  let p : ℕ → ℝ := fun n => accProb P (γ n)
  have hm := flow_p_mono hP hγ
  have hmn : Monotone p := by
    intro m n hmn
    exact hm (by simp) (by simp) (by exact_mod_cast hmn)
  have hb : BddAbove (range p) := ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact accProb_le_one hP (hγ.sphere n (by simp))⟩
  let L := ⨆ n, p n
  have hL : L ≤ 1 := ciSup_le fun n => accProb_le_one hP (hγ.sphere n (by simp))
  have hpL (t : ℝ) (ht : 0 ≤ t) : accProb P (γ t) ≤ L := by
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact (hm ht (by simp) hn).trans (le_ciSup hb n)
  have he : L = 1 := by
    by_contra hne
    have hlt : L < 1 := lt_of_le_of_ne hL hne
    let β := 16 * (accProb P (γ 0) - 3 / 2 * α) * (1 - L)
    have hβ : 0 < β := by dsimp [β]; positivity
    have hd (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
        HasDerivWithinAt (fun t => accProb P (γ t) - β * t)
          (‖gradAcc P (γ t)‖ ^ 2 - β) (Ici 0) t := by
      apply (flow_hasDerivAt_p hP hγ ht).sub
      simpa using ((hasDerivAt_id t).const_mul β).hasDerivWithinAt (s := Ici 0)
    have hg : MonotoneOn (fun t => accProb P (γ t) - β * t) (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      · exact fun t ht => (hd t ht).continuousWithinAt
      · exact fun t ht => (hd t (interior_subset ht)).mono interior_subset
      · intro t ht
        have ht' : 0 ≤ t := interior_subset ht
        have hlo := hm (by simp) ht' ht'
        have hup := hpL t ht'
        have hgap' := norm_gradAcc_sq_ge hP hgap (hγ.sphere t ht')
        have hm' := mul_le_mul (show accProb P (γ 0) - 3 / 2 * α ≤
            accProb P (γ t) - 3 / 2 * α by linarith)
          (show 1 - L ≤ 1 - accProb P (γ t) by linarith)
          (by linarith : 0 ≤ 1 - L) (by linarith : 0 ≤ accProb P (γ t) - 3 / 2 * α)
        dsimp [β]
        nlinarith
    let t := (2 - accProb P (γ 0)) / β
    have ht : 0 ≤ t := div_nonneg (by
      linarith [accProb_le_one hP (hγ.sphere 0 (by simp))]) hβ.le
    have hg' := hg (by simp) ht ht
    have hu := accProb_le_one hP (hγ.sphere t ht)
    have he' : β * t = 2 - accProb P (γ 0) := by
      dsimp [t]; field_simp
    simp only [mul_zero, sub_zero] at hg'
    linarith
  simpa [p, L, he] using tendsto_atTop_ciSup hmn hb

/-! ### D. The potential function -/

/-- The paper's potential `V(p) = arcsin(√((1-p)/(1-c)))/2`, the antiderivative of
`-1/(4√((p-c)(1-p)))`. -/
def Vpot (c p : ℝ) : ℝ := Real.arcsin (Real.sqrt ((1 - p) / (1 - c))) / 2

lemma Vpot_nonneg {c p : ℝ} (hp : p ≤ 1) : 0 ≤ Vpot c p := by
  have _ := hp
  exact div_nonneg (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)) (by norm_num)

lemma Vpot_le_pi_div_four (c p : ℝ) : Vpot c p ≤ Real.pi / 4 := by
  unfold Vpot
  linarith [Real.arcsin_le_pi_div_two (Real.sqrt ((1 - p) / (1 - c)))]

@[simp] lemma Vpot_one (c : ℝ) : Vpot c 1 = 0 := by
  simp [Vpot]

/-- `V` is antitone in `p` and continuous; at `p = 1` it vanishes, so
`V(p_n) → 0` when `p_n → 1`. -/
lemma Vpot_tendsto_zero {c : ℝ} (hc : c < 1) {p : ℕ → ℝ}
    (hp : Filter.Tendsto p Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => Vpot c (p n)) Filter.atTop (nhds 0) := by
  have _ := hc
  have hq : Filter.Tendsto (fun n => (1 - p n) / (1 - c)) Filter.atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 1)).sub hp).div_const (1 - c)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have hs' : Filter.Tendsto (fun n => Real.sqrt ((1 - p n) / (1 - c)))
      Filter.atTop (nhds 0) := by simpa [Function.comp_def] using hs
  have ha := Real.continuous_arcsin.continuousAt.tendsto.comp hs'
  simpa [Vpot, Function.comp_def] using ha.div_const 2

/-- Derivative of the potential on `(c, 1)`. -/
lemma hasDerivAt_Vpot {c p : ℝ} (hc : c < 1) (hp : p ∈ Ioo c 1) :
    HasDerivAt (Vpot c) (-(1 / (4 * Real.sqrt ((p - c) * (1 - p))))) p := by
  have hD : 0 < 1 - c := sub_pos.mpr hc
  have hx : 0 < (1 - p) / (1 - c) := div_pos (sub_pos.mpr hp.2) hD
  have hx1 : (1 - p) / (1 - c) < 1 := (div_lt_one hD).mpr (by linarith [hp.1])
  have hu : 0 < Real.sqrt ((1 - p) / (1 - c)) := Real.sqrt_pos.mpr hx
  have hu1 : Real.sqrt ((1 - p) / (1 - c)) < 1 := by
    nlinarith [Real.sq_sqrt hx.le]
  have hs := Real.sq_sqrt hx.le
  have hy : 0 < 1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2 := by nlinarith
  have hv : 0 < Real.sqrt (1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2) :=
    Real.sqrt_pos.mpr hy
  have hw : 0 < Real.sqrt ((p - c) * (1 - p)) :=
    Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr hp.1) (sub_pos.mpr hp.2))
  have hd : HasDerivAt (fun x : ℝ => (1 - x) / (1 - c)) (-1 / (1 - c)) p := by
    simpa using ((hasDerivAt_id p).const_sub 1).div_const (1 - c)
  have hu' := (Real.hasDerivAt_sqrt hx.ne').comp p hd
  have harc : HasDerivAt Real.arcsin
      (1 / Real.sqrt (1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2))
      (Real.sqrt ((1 - p) / (1 - c))) := by
    have hh := Real.sinPartialHomeomorph.hasStrictDerivAt_symm
      (show Real.sqrt ((1 - p) / (1 - c)) ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith, hu1⟩)
      (show Real.cos (Real.arcsin (Real.sqrt ((1 - p) / (1 - c)))) ≠ 0 by
        rw [Real.cos_arcsin]; exact hv.ne') (Real.hasStrictDerivAt_sin _)
    convert hh.hasDerivAt using 1
    · rfl
    · rw [Real.cos_arcsin, one_div]
  have ha := harc.comp p hu'
  have hprod : (1 - c) * Real.sqrt ((1 - p) / (1 - c)) *
      Real.sqrt (1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2) =
      Real.sqrt ((p - c) * (1 - p)) := by
    have hs' := Real.sq_sqrt hy.le
    have hs'' := Real.sq_sqrt (mul_pos (sub_pos.mpr hp.1) (sub_pos.mpr hp.2)).le
    have hxe : ((1 - p) / (1 - c)) * (1 - c) = 1 - p :=
      div_mul_cancel₀ _ hD.ne'
    have hA : ((1 - c) * Real.sqrt ((1 - p) / (1 - c))) ^ 2 =
        (1 - c) * (1 - p) := by
      rw [mul_pow, hs]
      calc
        _ = (1 - c) * (((1 - p) / (1 - c)) * (1 - c)) := by ring
        _ = _ := by rw [hxe]
    have hB : (1 - c) * (Real.sqrt (1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2)) ^ 2 = p - c := by
      nlinarith [hs, hs']
    have hC : ((1 - c) * Real.sqrt ((1 - p) / (1 - c)) *
        Real.sqrt (1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2)) ^ 2 =
        (p - c) * (1 - p) := by
      calc
        _ = (((1 - c) * Real.sqrt ((1 - p) / (1 - c))) ^ 2) *
            Real.sqrt (1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2) ^ 2 := by ring
        _ = (1 - p) * ((1 - c) * Real.sqrt (1 - Real.sqrt ((1 - p) / (1 - c)) ^ 2) ^ 2) := by rw [hA]; ring
        _ = _ := by rw [hB]; ring
    nlinarith [mul_pos (mul_pos hD hu) hv]
  convert ha.div_const 2 using 1
  · rfl
  · field_simp
    nlinarith [hprod]

/-! ### E. The chord bound -/

/-- **Chord bound** (the paper's arc-length estimate, integral-free form): under the
gap hypothesis with `c = 3α/2 < p_0 < 1`, for all `0 ≤ s ≤ t`,

    ‖γ t - γ s‖ ≤ V(p_s) - V(p_t).

Proof: for every unit `u`, the function `r ↦ Re⟪u, γ r⟫ + V(p_r)` is antitone on
`[0, ∞)`: its derivative is `Re⟪u, gradAcc⟫ - ṗ/(4√((p-c)(1-p))) ≤ ‖gradAcc‖ - ‖gradAcc‖² /(4√(⋯)) ≤ 0`
by Cauchy–Schwarz and the Łojasiewicz bound `‖gradAcc‖² ≥ 16(p-c)(1-p)`
(`norm_gradAcc_sq_ge`, using `p_r ≥ p_0 > c` from monotonicity and `p_r < 1` from
`flow_one_sub_p_ge`). Take `u := (γ t - γ s)/‖γ t - γ s‖`. -/
theorem flow_chord_bound (hP : IsAcceptanceProjection P) {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : SpectralGapHyp P α) (hγ : IsGlobalFlow P γ)
    (h0 : 3 / 2 * α < accProb P (γ 0)) (h1 : accProb P (γ 0) < 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖γ t - γ s‖ ≤
      Vpot (3 / 2 * α) (accProb P (γ s)) - Vpot (3 / 2 * α) (accProb P (γ t)) := by
  have _ := hα0
  let c := 3 / 2 * α
  have hc : c < 1 := h0.trans h1
  have hm := flow_p_mono hP hγ
  have hp (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) : accProb P (γ r) ∈ Ioo c 1 := by
    constructor
    · exact h0.trans_le (hm (by simp) hr hr)
    · have h := flow_one_sub_p_ge hP hγ hr
      have he := mul_pos (Real.exp_pos (-(16 * r))) (sub_pos.mpr h1)
      linarith
  have hv (v : H ι) : AntitoneOn
      (fun r => (⟪v, γ r⟫_ℂ).re + ‖v‖ * Vpot c (accProb P (γ r))) (Ici 0) := by
    let d := fun r => (⟪v, gradAcc P (γ r)⟫_ℂ).re + ‖v‖ *
      (-(1 / (4 * Real.sqrt ((accProb P (γ r) - c) * (1 - accProb P (γ r)))))) *
        ‖gradAcc P (γ r)‖ ^ 2
    have hd (r : ℝ) (hr : r ∈ Ici (0 : ℝ)) :
        HasDerivWithinAt (fun r => (⟪v, γ r⟫_ℂ).re + ‖v‖ * Vpot c (accProb P (γ r)))
          (d r) (Ici 0) r := by
      have hi := (hasDerivWithinAt_const r (Ici 0) v).inner ℂ (hγ.deriv r hr)
      have hi' := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt r hi
      have hv' := (hasDerivAt_Vpot hc (hp r hr)).comp_hasDerivWithinAt r
        (flow_hasDerivAt_p hP hγ hr)
      convert hi'.add (hv'.const_mul ‖v‖) using 1
      · rfl
      · simp [d, inner_zero_left, mul_assoc]
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · exact fun r hr => (hd r hr).continuousWithinAt
    · exact fun r hr => (hd r (interior_subset hr)).mono interior_subset
    · intro r hr
      have hr' := interior_subset hr
      have hpr := hp r hr'
      let A := Real.sqrt ((accProb P (γ r) - c) * (1 - accProb P (γ r)))
      have hA : 0 < A := Real.sqrt_pos.mpr
        (mul_pos (sub_pos.mpr hpr.1) (sub_pos.mpr hpr.2))
      have hAsq : A ^ 2 = (accProb P (γ r) - c) * (1 - accProb P (γ r)) :=
        Real.sq_sqrt (mul_pos (sub_pos.mpr hpr.1) (sub_pos.mpr hpr.2)).le
      have hg := norm_gradAcc_sq_ge hP hgap (hγ.sphere r hr')
      change 16 * (accProb P (γ r) - c) * (1 - accProb P (γ r)) ≤ _ at hg
      have hng := norm_nonneg (gradAcc P (γ r))
      have hb : 4 * A ≤ ‖gradAcc P (γ r)‖ := by nlinarith
      have hmul : ‖gradAcc P (γ r)‖ * (4 * A) ≤ ‖gradAcc P (γ r)‖ ^ 2 := by
        nlinarith [mul_nonneg hng (sub_nonneg.mpr hb)]
      have hdiv : ‖gradAcc P (γ r)‖ ≤ ‖gradAcc P (γ r)‖ ^ 2 / (4 * A) :=
        (le_div_iff₀ (by positivity)).mpr hmul
      have hi := re_inner_le_norm (𝕜 := ℂ) v (gradAcc P (γ r))
      change (⟪v, gradAcc P (γ r)⟫_ℂ).re ≤ ‖v‖ * ‖gradAcc P (γ r)‖ at hi
      have hmul' := mul_le_mul_of_nonneg_left hdiv (norm_nonneg v)
      dsimp [d]
      change (⟪v, gradAcc P (γ r)⟫_ℂ).re + ‖v‖ * (-(1 / (4 * A))) *
        ‖gradAcc P (γ r)‖ ^ 2 ≤ 0
      have heq : ‖v‖ * (-(1 / (4 * A))) * ‖gradAcc P (γ r)‖ ^ 2 =
          -(‖v‖ * (‖gradAcc P (γ r)‖ ^ 2 / (4 * A))) := by ring
      rw [heq]
      linarith
  have hh := hv (γ t - γ s) hs (le_trans hs hst) hst
  have hi : (⟪γ t - γ s, γ t⟫_ℂ).re - (⟪γ t - γ s, γ s⟫_ℂ).re =
      ‖γ t - γ s‖ ^ 2 := by
    rw [← Complex.sub_re, ← inner_sub_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hn := norm_nonneg (γ t - γ s)
  by_cases hz : ‖γ t - γ s‖ = 0
  · rw [hz]
    have hpst := hm hs (le_trans hs hst) hst
    unfold Vpot
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.arcsin_le_arcsin
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · have hn' : 0 < ‖γ t - γ s‖ := lt_of_le_of_ne hn (Ne.symm hz)
    have hineq : ‖γ t - γ s‖ ^ 2 ≤ ‖γ t - γ s‖ *
        (Vpot c (accProb P (γ s)) - Vpot c (accProb P (γ t))) := by linarith
    nlinarith

/-! ### F. Convergence to a limit in `G` -/

/-- The flow converges along natural times to a certainty state. The potential
bounds the chord from the initial vector to this same limit. -/
theorem flow_limit_tendsto (hP : IsAcceptanceProjection P) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 2 / 3) (hgap : SpectralGapHyp P α) (hγ : IsGlobalFlow P γ)
    (h0 : 3 / 2 * α < accProb P (γ 0)) (h1 : accProb P (γ 0) < 1) :
    ∃ φ : H ι, Filter.Tendsto (fun n : ℕ => γ (n : ℝ)) Filter.atTop (nhds φ) ∧
      ‖φ‖ = 1 ∧ accProb P φ = 1 ∧
      ‖γ 0 - φ‖ ≤ Vpot (3 / 2 * α) (accProb P (γ 0)) := by
  have hc : 3 / 2 * α < 1 := by linarith only [hα]
  have hp := flow_p_tendsto_one hP hgap hγ h0
  have hv := Vpot_tendsto_zero hc hp
  have hch (m n : ℕ) (hmn : m ≤ n) :
      dist (γ m) (γ n) ≤ Vpot (3 / 2 * α) (accProb P (γ m)) := by
    have hh := flow_chord_bound hP hα0 hgap hγ h0 h1
      (s := (m : ℝ)) (t := (n : ℝ)) (by positivity) (by exact_mod_cast hmn)
    have hn := Vpot_nonneg (c := 3 / 2 * α)
      (accProb_le_one hP (hγ.sphere n (by simp)))
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  have hca : CauchySeq (fun n : ℕ => γ n) :=
    cauchySeq_of_le_tendsto_0' _ hch hv
  obtain ⟨φ, hφ⟩ := cauchySeq_tendsto_of_complete hca
  refine ⟨φ, hφ, ?_, ?_, ?_⟩
  · have hn := hφ.norm
    have he : (fun n : ℕ => ‖γ (n : ℝ)‖) = fun _ => (1 : ℝ) := by
      funext n; exact hγ.sphere n (by simp)
    rw [he] at hn
    exact tendsto_nhds_unique hn tendsto_const_nhds
  · have ha := (contDiff_accProb (P := P)).continuous.continuousAt.tendsto.comp hφ
    exact tendsto_nhds_unique ha hp
  · have hh : Filter.Tendsto (fun n : ℕ => ‖γ 0 - γ (n : ℝ)‖) Filter.atTop
        (nhds ‖γ 0 - φ‖) := (tendsto_const_nhds.sub hφ).norm
    apply le_of_tendsto hh
    exact Filter.Eventually.of_forall fun n => by
      have h := hch 0 n (Nat.zero_le n)
      simpa [dist_eq_norm] using h

/-- The limit gives a unit certainty state within chord distance `V(p_0)`. -/
theorem flow_limit (hP : IsAcceptanceProjection P) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < 2 / 3) (hgap : SpectralGapHyp P α) (hγ : IsGlobalFlow P γ)
    (h0 : 3 / 2 * α < accProb P (γ 0)) (h1 : accProb P (γ 0) < 1) :
    ∃ φ : H ι, ‖φ‖ = 1 ∧ accProb P φ = 1 ∧
      ‖γ 0 - φ‖ ≤ Vpot (3 / 2 * α) (accProb P (γ 0)) := by
  obtain ⟨φ, _, hφ, hpφ, hchord⟩ := flow_limit_tendsto hP hα0 hα hgap hγ h0 h1
  exact ⟨φ, hφ, hpφ, hchord⟩

/-- The projective angle on a finite segment of the flow is bounded by the
drop in the potential. Apply the path-length comparison to the chord estimate
on every subinterval of the segment. -/
theorem flow_angle_bound (hP : IsAcceptanceProjection P) {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : SpectralGapHyp P α) (hγ : IsGlobalFlow P γ)
    (h0 : 3 / 2 * α < accProb P (γ 0)) (h1 : accProb P (γ 0) < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.arccos ‖inner ℂ (γ 0) (γ t)‖ ≤
      Vpot (3 / 2 * α) (accProb P (γ 0)) - Vpot (3 / 2 * α) (accProb P (γ t)) := by
  apply projective_angle_le_of_chord_bound (γ := γ)
    (v := fun r => Vpot (3 / 2 * α) (accProb P (γ r))) ht
  · intro r hr
    exact (hγ.deriv r hr.1).continuousWithinAt.mono (fun _ hur => hur.1)
  · exact fun r hr => hγ.sphere r hr.1
  · intro s hs u _ hsu
    rw [norm_sub_rev]
    exact flow_chord_bound hP hα0 hgap hγ h0 h1 hs.1 hsu

/-- Angular conclusion of Theorem 3.4 in finite dimensions under the polynomial gap
hypothesis. Above the threshold `3α/2`, the flow limit is a unit certainty state
whose projective angle to the input is at most the initial potential. -/
theorem angular_witness_of_gap (hP : IsAcceptanceProjection P)
    {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hgap : SpectralGapHyp P α)
    {ψ : H ι} (hψ : ‖ψ‖ = 1) (hhigh : 3 / 2 * α < accProb P ψ) :
    ∃ φ : H ι, ‖φ‖ = 1 ∧ accProb P φ = 1 ∧
      Real.arccos ‖inner ℂ ψ φ‖ ≤ Vpot (3 / 2 * α) (accProb P ψ) := by
  rcases eq_or_lt_of_le (accProb_le_one hP hψ) with hcert | hlt
  · refine ⟨ψ, hψ, hcert, ?_⟩
    rw [hcert, Vpot_one, inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  · obtain ⟨γ, hinit, hsphere, hderiv⟩ := exists_global_flow hP hψ
    have hγ : IsGlobalFlow P γ := ⟨hsphere, hderiv⟩
    have h0 : 3 / 2 * α < accProb P (γ 0) := by simpa [hinit] using hhigh
    have h1 : accProb P (γ 0) < 1 := by simpa [hinit] using hlt
    obtain ⟨φ, hlim, hφ, hpφ, _⟩ := flow_limit_tendsto hP hα0 hα hgap hγ h0 h1
    refine ⟨φ, hφ, hpφ, ?_⟩
    rw [← hinit]
    have hlimitAngle : Filter.Tendsto
        (fun n : ℕ => Real.arccos ‖inner ℂ (γ 0) (γ (n : ℝ))‖) Filter.atTop
        (nhds (Real.arccos ‖inner ℂ (γ 0) φ‖)) :=
      (Real.continuous_arccos.comp (innerSL ℂ (γ 0)).continuous.norm).continuousAt.tendsto.comp hlim
    apply le_of_tendsto hlimitAngle
    refine Filter.Eventually.of_forall fun n => ?_
    exact (flow_angle_bound hP hα0 hgap hγ h0 h1 (t := (n : ℝ)) (by positivity)).trans
      (sub_le_self _ (Vpot_nonneg (accProb_le_one hP (hγ.sphere n (by simp)))))

/-! ### G. Squared overlap from the chord estimate

With `θ := V(p_0) = arcsin(√(C(1-p_0)))/2 ≤ π/4` and two unit vectors at distance
`≤ θ`, the squared overlap is at least `(1 - θ²/2)² ≥ cos²(2θ) = 1 - C(1-p_0)`,
using `sin x ≥ x/2` on `[0, 1]`. -/

/-- `(1 - θ²/2)² ≥ 1 - sin²(2θ)` for `θ ∈ [0, π/4]`. -/
lemma one_sub_sq_half_sq_ge {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    1 - Real.sin (2 * θ) ^ 2 ≤ (1 - θ ^ 2 / 2) ^ 2 := by
  have ht : θ ≤ 1 := by linarith [Real.pi_le_four]
  have hs : θ / 2 ≤ Real.sin θ := by
    have h := Real.sin_ge_sub_cube h0
    have hsq : θ ^ 2 ≤ 1 := by nlinarith
    have hcube : θ ^ 3 ≤ θ := by nlinarith [mul_nonneg h0 (sub_nonneg.mpr hsq)]
    linarith
  have hc : 0 ≤ Real.cos (2 * θ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have he := Real.cos_two_mul θ
  have hid := Real.sin_sq_add_cos_sq θ
  have hc' : Real.cos (2 * θ) ≤ 1 - θ ^ 2 / 2 := by
    nlinarith [sq_nonneg (Real.sin θ - θ / 2)]
  have hi := Real.sin_sq_add_cos_sq (2 * θ)
  nlinarith [sq_nonneg (1 - θ ^ 2 / 2 - Real.cos (2 * θ))]

/-- Overlap from chord distance for unit vectors:
`‖ψ - φ‖ ≤ r ≤ √2  ⟹  ‖⟪ψ, φ⟫‖² ≥ (1 - r²/2)²`. -/
lemma overlap_of_chord {ψ φ : H ι} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) {r : ℝ}
    (hr : ‖ψ - φ‖ ≤ r) (hr2 : r ^ 2 ≤ 2) :
    (1 - r ^ 2 / 2) ^ 2 ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  have hn := norm_sub_sq (𝕜 := ℂ) ψ φ
  rw [hψ, hφ] at hn
  have hd : ‖ψ - φ‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hre := (le_abs_self (⟪ψ, φ⟫_ℂ).re).trans (Complex.abs_re_le_norm _)
  have ha : 0 ≤ 1 - r ^ 2 / 2 := by linarith
  have hb : 1 - r ^ 2 / 2 ≤ ‖⟪ψ, φ⟫_ℂ‖ := by
    change ‖ψ - φ‖ ^ 2 = 1 ^ 2 - 2 * (⟪ψ, φ⟫_ℂ).re + 1 ^ 2 at hn
    linarith
  exact pow_le_pow_left₀ ha hb 2

end

end GaussianTesting
