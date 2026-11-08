module

/-
Calculus of the acceptance probability (preparation for the gradient-flow proof of
Theorem 3.4).

Main results:
* `norm_tp2` — `‖ψ ⊗ φ‖ = ‖ψ‖ ‖φ‖`, hence `tp2` is a bounded bilinear map;
* `Kvec_eq_contr` — `K_ψψ` as a bounded ℝ-bilinear contraction, hence smooth in `ψ`;
* `hasFDerivAt_accProb` — the Fréchet derivative of `p` at any `ψ ∈ H` (not only on the
  sphere) is `v ↦ 4 Re⟪v, K_ψψ⟫`, i.e. eq:acceptance grad before projecting;
* `contDiff_accProb`, `contDiff_gradAcc` — smoothness (over ℝ);
* `lipschitzOnWith_gradAcc` — a Lipschitz bound for the vector field on `closedBall 0 2`
  (input to Picard–Lindelöf);
* `qProb_le_accProb` — `q(ψ) ≤ p(ψ)` for unit `ψ` (row-wise Cauchy–Schwarz), used for
  the a-priori bound `ṗ ≤ 16(1-p)` along the flow.
-/
public import GaussianTesting.GradientFlow.Lojasiewicz
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

variable {ι : Type*} [Fintype ι]

/-! ### `tp2` as a bounded bilinear map -/

/-- The elementary tensor has multiplicative norm. -/
lemma norm_tp2 (ψ φ : H ι) : ‖tp2 ψ φ‖ = ‖ψ‖ * ‖φ‖ := by
  have h := congrArg Complex.re (inner_tp2_tp2 ψ ψ φ φ)
  simp only [inner_self_eq_norm_sq_to_K] at h
  change ((‖tp2 ψ φ‖ : ℂ) ^ 2).re = ((‖ψ‖ : ℂ) ^ 2 * (‖φ‖ : ℂ) ^ 2).re at h
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul] at h
  nlinarith [norm_nonneg (tp2 ψ φ), norm_nonneg ψ, norm_nonneg φ,
    mul_nonneg (norm_nonneg ψ) (norm_nonneg φ)]

/-- `tp2` is a bounded ℂ-bilinear map. -/
lemma isBoundedBilinearMap_tp2 :
    IsBoundedBilinearMap ℂ (fun p : H ι × H ι => tp2 p.1 p.2) := by
  refine ⟨?_, ?_, ?_, ?_, 1, by norm_num, ?_⟩
  · intro x z y; ext p; simp [add_mul]
  · intro c x y; ext p; simp [mul_assoc]
  · intro x y z; ext p; simp [mul_add]
  · intro c x y; ext p; simp [mul_left_comm]
  · intro x y; simp [norm_tp2]

/-! ### The contraction `(φ, y) ↦ (I ⊗ ⟨φ|) y` -/

/-- The sesquilinear contraction sending `(φ, y)` to the vector
`i ↦ ∑ j, conj (φ j) * y (i, j)`; ℝ-bilinear (conjugate-linear in `φ`). -/
def contr (φ : H ι) (y : H2 ι) : H ι :=
  WithLp.toLp 2 fun i => ∑ j, conj (φ j) * y (i, j)

@[simp] lemma contr_apply (φ : H ι) (y : H2 ι) (i : ι) :
    contr φ y i = ∑ j, conj (φ j) * y (i, j) := rfl

private lemma inner_tp2_contr (v φ : H ι) (y : H2 ι) :
    ⟪tp2 v φ, y⟫_ℂ = ⟪v, contr φ y⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, tp2_apply, contr_apply,
    Fintype.sum_prod_type, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Row-wise Cauchy–Schwarz: the contraction is bounded. -/
lemma norm_contr_le (φ : H ι) (y : H2 ι) : ‖contr φ y‖ ≤ ‖φ‖ * ‖y‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (tp2 (contr φ y) φ) y
  rw [inner_tp2_contr, inner_self_eq_norm_sq_to_K, norm_tp2] at h
  change ‖(‖contr φ y‖ : ℂ) ^ 2‖ ≤ _ at h
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] at h
  by_cases hz : ‖contr φ y‖ = 0
  · rw [hz]; positivity
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp
    nlinarith only [h]

/-- The contraction is a bounded ℝ-bilinear map. -/
lemma isBoundedBilinearMap_contr :
    IsBoundedBilinearMap ℝ (fun p : H ι × H2 ι => contr p.1 p.2) := by
  refine ⟨?_, ?_, ?_, ?_, 1, by norm_num, ?_⟩
  · intro x z y; ext i; simp [contr_apply, map_add, add_mul, Finset.sum_add_distrib]
  · intro c x y; ext i
    simp [contr_apply, PiLp.smul_apply, Complex.real_smul, map_mul,
      ← Finset.mul_sum, mul_assoc]
  · intro x y z; ext i; simp [contr_apply, mul_add, Finset.sum_add_distrib]
  · intro c x y; ext i
    simp [contr_apply, PiLp.smul_apply, Complex.real_smul,
      ← Finset.mul_sum, mul_left_comm]
  · intro x y; simpa using norm_contr_le x y

/-- `K_ψψ` through the contraction. -/
lemma Kvec_eq_contr (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) :
    Kvec P ψ = contr ψ (P (tp2 ψ ψ)) := rfl

/-! ### Smoothness -/

variable {P : H2 ι →ₗ[ℂ] H2 ι}

private lemma smooth_tp : ContDiff ℝ (⊤ : ℕ∞) (fun ψ : H ι => tp2 ψ ψ) := by
  exact (show ContDiff ℂ (⊤ : ℕ∞) (fun ψ : H ι => tp2 ψ ψ) from
    (isBoundedBilinearMap_tp2 (ι := ι)).contDiff.comp (contDiff_id.prodMk contDiff_id)).restrict_scalars ℝ

/-- The acceptance probability is smooth (as a real-valued function on `H`). -/
lemma contDiff_accProb : ContDiff ℝ (⊤ : ℕ∞) (accProb P) := by
  exact Complex.reCLM.contDiff.comp
    (smooth_tp.inner ℂ ((P.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp smooth_tp))

/-- `ψ ↦ K_ψψ` is smooth over ℝ. -/
lemma contDiff_Kvec : ContDiff ℝ (⊤ : ℕ∞) (fun ψ : H ι => Kvec P ψ) := by
  exact isBoundedBilinearMap_contr.contDiff.comp
    (contDiff_id.prodMk ((P.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp smooth_tp))

/-- The gradient vector field is smooth over ℝ. -/
lemma contDiff_gradAcc : ContDiff ℝ (⊤ : ℕ∞) (fun ψ : H ι => gradAcc P ψ) := by
  exact (contDiff_Kvec.sub ((Complex.ofRealCLM.contDiff.comp contDiff_accProb).smul
    contDiff_id)).const_smul (4 : ℂ)

/-! ### The Fréchet derivative of `p` -/

/-- The derivative functional `v ↦ 4 Re⟪v, K_ψψ⟫` of the acceptance probability,
as a continuous ℝ-linear map. (Note `Re⟪v, K⟫ = Re⟪K, v⟫`.) -/
def accProbDeriv (P : H2 ι →ₗ[ℂ] H2 ι) (ψ : H ι) : H ι →L[ℝ] ℝ :=
  (4 : ℝ) • (Complex.reCLM.comp (((innerSL ℂ) (Kvec P ψ)).restrictScalars ℝ))

@[simp] lemma accProbDeriv_apply (P : H2 ι →ₗ[ℂ] H2 ι) (ψ v : H ι) :
    accProbDeriv P ψ v = 4 * (⟪Kvec P ψ, v⟫_ℂ).re := rfl

/-- eq:acceptance grad (ambient form): `p` has Fréchet derivative
`v ↦ 4 Re⟪v, K_ψψ⟫` at every `ψ ∈ H`. Needs `P` symmetric and swap-commuting. -/
theorem hasFDerivAt_accProb (hP : IsAcceptanceProjection P) (ψ : H ι) :
    HasFDerivAt (accProb P) (accProbDeriv P ψ) ψ := by
  let D := (isBoundedBilinearMap_tp2 (ι := ι)).deriv (ψ, ψ) |>.comp
    ((ContinuousLinearMap.id ℂ (H ι)).prod (ContinuousLinearMap.id ℂ (H ι)))
  have ht : HasFDerivAt (fun x : H ι => tp2 x x) (D.restrictScalars ℝ) ψ := by
    have hd : HasFDerivAt (fun x : H ι => (x, x))
        ((ContinuousLinearMap.id ℂ (H ι)).prod (ContinuousLinearMap.id ℂ (H ι))) ψ :=
      (hasFDerivAt_id ψ).prodMk (hasFDerivAt_id ψ)
    exact (HasFDerivAt.comp (f := fun x : H ι => (x, x)) ψ
      ((isBoundedBilinearMap_tp2 (ι := ι)).hasFDerivAt (ψ, ψ)) hd).restrictScalars ℝ
  have hp := (P.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp ψ ht
  have h := Complex.reCLM.hasFDerivAt.comp ψ (ht.inner ℂ hp)
  change HasFDerivAt (accProb P) _ ψ at h
  apply h.congr_fderiv
  ext v
  change (⟪tp2 ψ ψ, P (tp2 ψ v + tp2 v ψ)⟫_ℂ +
    ⟪tp2 ψ v + tp2 v ψ, P (tp2 ψ ψ)⟫_ℂ).re = 4 * (⟪Kvec P ψ, v⟫_ℂ).re
  have hs : ⟪tp2 ψ v, P (tp2 ψ ψ)⟫_ℂ = ⟪v, Kvec P ψ⟫_ℂ := by
    have he : ⟪tp2 ψ v, P (tp2 ψ ψ)⟫_ℂ =
        ⟪tp2 v ψ, P (tp2 ψ ψ)⟫_ℂ := by
      have hy : swap2 (P (tp2 ψ ψ)) = P (tp2 ψ ψ) := by
        rw [← hP.swap_comm, swap2_tp2]
      rw [← swap2_tp2 v ψ]
      calc
        _ = ⟪swap2 (tp2 v ψ), swap2 (P (tp2 ψ ψ))⟫_ℂ := by rw [hy]
        _ = _ := (swap2 (ι := ι)).inner_map_map _ _
    rw [he, inner_tp2_contr, ← Kvec_eq_contr]
  have ha : ⟪tp2 v ψ, P (tp2 ψ ψ)⟫_ℂ = ⟪v, Kvec P ψ⟫_ℂ := by
    rw [inner_tp2_contr, ← Kvec_eq_contr]
  have hb : ⟪tp2 ψ ψ, P (tp2 ψ v + tp2 v ψ)⟫_ℂ =
      conj ⟪tp2 ψ v + tp2 v ψ, P (tp2 ψ ψ)⟫_ℂ := by
    rw [inner_conj_symm, hP.symmetric]
  rw [hb, inner_add_left, hs, ha]
  have hr : (⟪v, Kvec P ψ⟫_ℂ).re = (⟪Kvec P ψ, v⟫_ℂ).re := by
    rw [← inner_conj_symm v (Kvec P ψ), Complex.conj_re]
  simp only [Complex.add_re, Complex.conj_re, hr]
  ring

/-- Derivative of `p` along a differentiable curve. -/
theorem hasDerivAt_accProb_comp {γ : ℝ → H ι} {γ' : H ι} {t : ℝ}
    (hP : IsAcceptanceProjection P) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => accProb P (γ s)) (4 * (⟪Kvec P (γ t), γ'⟫_ℂ).re) t := by
  exact (hasFDerivAt_accProb hP (γ t)).comp_hasDerivAt t hγ

/-- Along the flow direction, the derivative of `p` is the squared norm of the
gradient: `4 Re⟪gradAcc ψ, K_ψψ⟫ = ‖gradAcc ψ‖²` for unit `ψ`. -/
theorem deriv_accProb_gradAcc (hP : IsAcceptanceProjection P) {ψ : H ι}
    (hψ : ‖ψ‖ = 1) :
    4 * (⟪Kvec P ψ, gradAcc P ψ⟫_ℂ).re = ‖gradAcc P ψ‖ ^ 2 := by
  have hk : ⟪Kvec P ψ, ψ⟫_ℂ = (accProb P ψ : ℂ) := by
    rw [← inner_conj_symm, inner_psi_Kvec, inner_tp2_P_self hP.symmetric,
      Complex.conj_ofReal]
  rw [norm_gradAcc_sq hP hψ]
  simp only [gradAcc, inner_smul_right, inner_sub_right, inner_Kvec_self, hk]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

/-! ### Lipschitz bound for Picard–Lindelöf -/

private lemma bilip {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {b : E × F → G} (hb : IsBoundedBilinearMap 𝕜 b)
    {s : Set (H ι)} (hs : IsCompact s) {f : H ι → E} {g : H ι → F}
    (cf : ContinuousOn f s) (cg : ContinuousOn g s)
    (lf : ∃ K, LipschitzOnWith K f s) (lg : ∃ K, LipschitzOnWith K g s) :
    ∃ K, LipschitzOnWith K (fun x => b (f x, g x)) s := by
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuousOn cf
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn cg
  obtain ⟨Kf, hf⟩ := lf
  obtain ⟨Kg, hg⟩ := lg
  obtain ⟨C, hC, hc⟩ := hb.bound
  let L := C * (max A 0 * (Kg : ℝ) + max B 0 * (Kf : ℝ))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨Real.toNNReal L, ?_⟩
  rw [lipschitzOnWith_iff_norm_sub_le] at hf hg ⊢
  intro x hx y hy
  rw [Real.coe_toNNReal _ hL]
  have he : b (f x, g x) - b (f y, g y) =
      b (f x, g x - g y) + b (f x - f y, g y) := by
    rw [hb.map_sub_left, hb.map_sub_right]; abel
  rw [he]
  calc
    _ ≤ ‖b (f x, g x - g y)‖ + ‖b (f x - f y, g y)‖ := norm_add_le _ _
    _ ≤ C * ‖f x‖ * ‖g x - g y‖ + C * ‖f x - f y‖ * ‖g y‖ :=
      add_le_add (hc _ _) (hc _ _)
    _ ≤ C * (max A 0) * ((Kg : ℝ) * ‖x - y‖) +
        C * ((Kf : ℝ) * ‖x - y‖) * (max B 0) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left ((hA x hx).trans (le_max_left _ _))
          hC.le) (hg hx hy) (norm_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left (hf hx hy) hC.le)
          ((hB y hy).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ = L * ‖x - y‖ := by dsimp [L]; ring

/-- The vector field is Lipschitz on the ball of radius 2 (with some constant). -/
theorem lipschitzOnWith_gradAcc :
    ∃ K : NNReal, LipschitzOnWith K (fun ψ : H ι => gradAcc P ψ)
      (Metric.closedBall 0 2) := by
  let s := Metric.closedBall (0 : H ι) 2
  have hs : IsCompact s := isCompact_closedBall _ _
  have lid : ∃ K, LipschitzOnWith K (id : H ι → H ι) s :=
    ⟨1, LipschitzWith.id.lipschitzOnWith⟩
  have lt : ∃ K, LipschitzOnWith K (fun x : H ι => tp2 x x) s :=
    bilip isBoundedBilinearMap_tp2 hs continuous_id.continuousOn
      continuous_id.continuousOn lid lid
  obtain ⟨Kt, ht⟩ := lt
  have ly : ∃ K, LipschitzOnWith K (fun x : H ι => P (tp2 x x)) s :=
    ⟨_, P.toContinuousLinearMap.lipschitzWith.comp_lipschitzOnWith ht⟩
  have cy : Continuous (fun x : H ι => P (tp2 x x)) :=
    P.toContinuousLinearMap.continuous.comp smooth_tp.continuous
  have lk := bilip isBoundedBilinearMap_contr hs continuous_id.continuousOn
    cy.continuousOn lid ly
  have li := bilip (isBoundedBilinearMap_inner (𝕜 := ℂ) (E := H2 ι)) hs
    smooth_tp.continuous.continuousOn cy.continuousOn ⟨Kt, ht⟩ ly
  obtain ⟨Ki, hi⟩ := li
  have lp : ∃ K, LipschitzOnWith K (fun x : H ι => (accProb P x : ℂ)) s :=
    ⟨_, Complex.ofRealCLM.lipschitzWith.comp_lipschitzOnWith
      (Complex.reCLM.lipschitzWith.comp_lipschitzOnWith hi)⟩
  have lm := bilip (isBoundedBilinearMap_smul (𝕜 := ℂ) (E := H ι)) hs
    (Complex.ofRealCLM.continuous.comp contDiff_accProb.continuous).continuousOn
    continuous_id.continuousOn lp lid
  obtain ⟨Kk, hk⟩ := lk
  obtain ⟨Km, hm⟩ := lm
  exact ⟨_, (((4 : ℂ) • ContinuousLinearMap.id ℂ (H ι)).lipschitzWith.comp_lipschitzOnWith
    (hk.sub hm))⟩

/-- The vector field is bounded on the ball of radius 2 (with some constant). -/
theorem norm_gradAcc_le :
    ∃ M : ℝ, 0 < M ∧ ∀ ψ : H ι, ψ ∈ Metric.closedBall (0 : H ι) 2 →
      ‖gradAcc P ψ‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : H ι) 2).exists_bound_of_continuousOn
    contDiff_gradAcc.continuous.continuousOn
  exact ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun ψ hψ => (hM ψ hψ).trans (le_max_left _ _)⟩

/-! ### `q ≤ p` -/

/-- Row-wise Cauchy–Schwarz: `q(ψ) = ‖K_ψψ‖² ≤ ‖P ψ⊗ψ‖² = p(ψ)` for unit `ψ`. -/
theorem qProb_le_accProb (hP : IsAcceptanceProjection P) {ψ : H ι} (hψ : ‖ψ‖ = 1) :
    qProb P ψ ≤ accProb P ψ := by
  have hi : P (P (tp2 ψ ψ)) = P (tp2 ψ ψ) :=
    LinearMap.congr_fun hP.idem (tp2 ψ ψ)
  have hp : accProb P ψ = ‖P (tp2 ψ ψ)‖ ^ 2 := by
    unfold accProb
    rw [← hi, ← hP.symmetric, hi]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h := norm_contr_le ψ (P (tp2 ψ ψ))
  rw [← Kvec_eq_contr, hψ, one_mul] at h
  unfold qProb
  change RCLike.re ⟪Kvec P ψ, Kvec P ψ⟫_ℂ ≤ _
  rw [inner_self_eq_norm_sq, hp]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-! ### Radial derivative (for sphere invariance of the flow)

`Re⟪ψ, gradAcc ψ⟫ = 4 p(ψ)(1 - ‖ψ‖²)`, which vanishes on the unit sphere. -/

theorem re_inner_gradAcc (hP : IsAcceptanceProjection P) (ψ : H ι) :
    (⟪ψ, gradAcc P ψ⟫_ℂ).re = 4 * accProb P ψ * (1 - ‖ψ‖ ^ 2) := by
  have hk : ⟪ψ, Kvec P ψ⟫_ℂ = (accProb P ψ : ℂ) :=
    (inner_psi_Kvec P ψ).trans (inner_tp2_P_self hP.symmetric ψ)
  simp only [gradAcc, inner_smul_right, inner_sub_right, hk,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  ring

end

end GaussianTesting
