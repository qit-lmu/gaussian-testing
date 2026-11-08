module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Affine charts for rays of a complex Hilbert space

For a fixed vector `u`, every ray not orthogonal to `u` has a unique representative
`w` with `⟪u,w⟫ = 1`. These representatives form an affine hyperplane. Division
by the overlap gives the changes of coordinates, and normalization of `w` gives
a smooth section of the unit sphere over the chart.
-/

@[expose] public section

namespace GaussianTesting

open Set Topology
open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Equip Mathlib's projectivization with the quotient topology of the nonzero vectors. -/
instance rayTopology : TopologicalSpace (Projectivization ℂ H) :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ : {x : H // x ≠ 0} → _) inferInstance

theorem isQuotientMap_rayMk :
    IsQuotientMap (Projectivization.mk' ℂ : {x : H // x ≠ 0} → Projectivization ℂ H) :=
  ⟨⟨rfl⟩, fun q => ⟨⟨q.rep, q.rep_nonzero⟩, q.mk_rep⟩⟩

/-- Divide by the overlap with `u` to take coordinates in the affine hyperplane. -/
def rayAffine (u x : H) : H := (inner ℂ u x)⁻¹ • x

theorem rayAffine_smul (u x : H) {a : ℂ} (ha : a ≠ 0) :
    rayAffine u (a • x) = rayAffine u x := by
  simp only [rayAffine, inner_smul_right, mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ ha,
    mul_one]

/-- The chart map on rays. Its value is zero outside the chart domain. -/
def rayChart (u : H) (q : Projectivization ℂ H) : H :=
  Projectivization.lift (fun x => rayAffine u (x : H)) (by
    intro a b t heq
    have ht : t ≠ 0 := by intro hz; exact a.2 (by simpa [hz] using heq)
    rw [heq, rayAffine_smul _ _ ht]) q

@[simp] theorem rayChart_mk (u x : H) (hx : x ≠ 0) :
    rayChart u (Projectivization.mk ℂ x hx) = rayAffine u x := rfl

/-- The open set of nonorthogonal rays. The condition on the representative is
invariant under nonzero scalar multiplication. -/
def rayChartDomain (u : H) : Set (Projectivization ℂ H) :=
  {q | inner ℂ u q.rep ≠ 0}

@[simp] theorem mem_rayChartDomain_mk (u x : H) (hx : x ≠ 0) :
    Projectivization.mk ℂ x hx ∈ rayChartDomain u ↔ inner ℂ u x ≠ 0 := by
  obtain ⟨a, h⟩ := Projectivization.exists_smul_eq_mk_rep (K := ℂ) x hx
  change inner ℂ u (Projectivization.mk ℂ x hx).rep ≠ 0 ↔ _
  rw [← h, Units.smul_def, inner_smul_right]
  simp

theorem isOpen_rayChartDomain (u : H) : IsOpen (rayChartDomain u) := by
  apply isOpen_coinduced.mpr
  have h : (Projectivization.mk' ℂ) ⁻¹' rayChartDomain u =
      {x : {x : H // x ≠ 0} | inner ℂ u (x : H) ≠ 0} := by
    ext x
    exact mem_rayChartDomain_mk u _ x.property
  rw [h]
  exact isOpen_ne_fun ((innerSL ℂ u).continuous.comp continuous_subtype_val) continuous_const

theorem exists_rayChartDomain (q : Projectivization ℂ H) : ∃ u : H, q ∈ rayChartDomain u :=
  ⟨q.rep, inner_self_ne_zero.mpr q.rep_nonzero⟩

theorem inner_rayChart (u : H) (q : Projectivization ℂ H) (hq : q ∈ rayChartDomain u) :
    inner ℂ u (rayChart u q) = 1 := by
  rw [← q.mk_rep, rayChart_mk, rayAffine, inner_smul_right, inv_mul_cancel₀ hq]

theorem rayChart_ne_zero (u : H) (q : Projectivization ℂ H) (hq : q ∈ rayChartDomain u) :
    rayChart u q ≠ 0 := by
  intro h
  simpa [h] using inner_rayChart u q hq

@[simp] theorem mk_rayChart (u : H) (q : Projectivization ℂ H) (hq : q ∈ rayChartDomain u) :
    Projectivization.mk ℂ (rayChart u q) (rayChart_ne_zero u q hq) = q := by
  conv_rhs => rw [← q.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  use (inner ℂ u q.rep)⁻¹
  rw [← q.mk_rep, rayChart_mk]
  simp [rayAffine]

theorem rayChart_inj {u : H} {q r : Projectivization ℂ H} (hq : q ∈ rayChartDomain u)
    (hr : r ∈ rayChartDomain u) (he : rayChart u q = rayChart u r) : q = r := by
  rw [← mk_rayChart u q hq, ← mk_rayChart u r hr]
  simp [he]

/-- Smoothness of the ambient coordinate formula on its domain. -/
theorem contDiffAt_rayAffine (u x : H) (hx : inner ℂ u x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (rayAffine u) x :=
  (((innerSL ℂ u).restrictScalars ℝ).contDiff.contDiffAt.inv hx).smul contDiffAt_id

/-- Normalize an affine representative to choose a representative on the unit sphere. -/
def rayChartSection (w : H) : H := (‖w‖ : ℂ)⁻¹ • w

theorem contDiffAt_rayChartSection (w : H) (hw : w ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) rayChartSection w := by
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : H => (‖x‖ : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w (contDiffAt_norm ℂ hw)
  exact (hn.inv (by exact_mod_cast norm_ne_zero_iff.mpr hw)).smul contDiffAt_id

theorem norm_rayChartSection (w : H) (hw : w ≠ 0) : ‖rayChartSection w‖ = 1 := by
  simp [rayChartSection, norm_smul, Complex.norm_real,
    norm_ne_zero_iff.mpr hw]

theorem mk_rayChartSection (w : H) (hw : w ≠ 0) :
    Projectivization.mk ℂ (rayChartSection w) (by
      have := norm_rayChartSection w hw
      intro hz
      simp [hz] at this) = Projectivization.mk ℂ w hw :=
  (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨_, rfl⟩

theorem rayChartSection_rayChart_mk (u x : H) (hx : ‖x‖ = 1) (hn : x ≠ 0)
    (hu : inner ℂ u x ≠ 0) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ rayChartSection (rayChart u (Projectivization.mk ℂ x hn)) = z • x := by
  have hw := rayChart_ne_zero u _ ((mem_rayChartDomain_mk u x hn).mpr hu)
  obtain ⟨z, hz⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp
    ((mk_rayChartSection _ hw).trans (mk_rayChart u _ ((mem_rayChartDomain_mk u x hn).mpr hu)))
  refine ⟨z, ?_, hz.symm⟩
  calc
    ‖z‖ = ‖z • x‖ := by rw [norm_smul, hx, mul_one]
    _ = ‖rayChartSection (rayChart u (Projectivization.mk ℂ x hn))‖ := congrArg norm hz
    _ = 1 := norm_rayChartSection _ hw

/-- Continuity of the quotient chart on its open domain. -/
theorem continuousOn_rayChart (u : H) : ContinuousOn (rayChart u) (rayChartDomain u) := by
  apply (isQuotientMap_rayMk.continuousOn_isOpen_iff (isOpen_rayChartDomain u)).mpr
  intro x hx
  have hn := (mem_rayChartDomain_mk u x x.property).mp hx
  exact ((contDiffAt_rayAffine u x hn).continuousAt.comp continuous_subtype_val.continuousAt).continuousWithinAt

/-- The inverse chart sends an affine representative to its ray. -/
def rayChartHomeomorph (u : H) :
    rayChartDomain u ≃ₜ {w : H // inner ℂ u w = 1} where
  toFun q := ⟨rayChart u q, inner_rayChart u q q.property⟩
  invFun w := by
    have hw : (w : H) ≠ 0 := by intro hz; simpa [hz] using w.property
    exact ⟨Projectivization.mk ℂ w hw, (mem_rayChartDomain_mk u _ hw).mpr
      (w.property.trans_ne one_ne_zero)⟩
  left_inv q := Subtype.ext (mk_rayChart u q q.property)
  right_inv w := by
    apply Subtype.ext
    change rayAffine u w = w
    simp [rayAffine, w.property]
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp (continuousOn_rayChart u)).subtype_mk _
  continuous_invFun := by
    have hf : Continuous (fun w : {w : H // inner ℂ u w = 1} =>
        (⟨(w : H), (show (w : H) ≠ 0 from fun hz => by simpa [hz] using w.property)⟩ :
          {x : H // x ≠ 0})) := continuous_subtype_val.subtype_mk _
    exact (isQuotientMap_rayMk.continuous.comp hf).subtype_mk _

/-- On an overlap, changing from chart `u` to chart `v` divides the first
representative by its overlap with `v`. -/
theorem rayChart_transition (u v : H) (q : Projectivization ℂ H) (hu : q ∈ rayChartDomain u) :
    rayChart v q = rayAffine v (rayChart u q) := by
  conv_lhs => rw [← mk_rayChart u q hu, rayChart_mk]

theorem contDiffOn_rayTransition (v : H) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rayAffine v) {w | inner ℂ v w ≠ 0} :=
  fun w hw => (contDiffAt_rayAffine v w hw).contDiffWithinAt

theorem rayChartSection_inner_ne_zero (u w : H) (hw : inner ℂ u w ≠ 0) :
    inner ℂ u (rayChartSection w) ≠ 0 := by
  have hw' : w ≠ 0 := by intro h; simp [h] at hw
  rw [rayChartSection, inner_smul_right]
  exact mul_ne_zero (inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hw')) hw

/-- Any two rays share a chart, including when they are orthogonal. -/
theorem exists_common_rayChartDomain (q r : Projectivization ℂ H) :
    ∃ u : H, q ∈ rayChartDomain u ∧ r ∈ rayChartDomain u := by
  by_cases h : inner ℂ q.rep r.rep = 0
  · refine ⟨q.rep + r.rep, ?_, ?_⟩
    · change inner ℂ (q.rep + r.rep) q.rep ≠ 0
      rw [inner_add_left, inner_eq_zero_symm.mp h, add_zero]
      exact inner_self_ne_zero.mpr q.rep_nonzero
    · change inner ℂ (q.rep + r.rep) r.rep ≠ 0
      rw [inner_add_left, h, zero_add]
      exact inner_self_ne_zero.mpr r.rep_nonzero
  · exact ⟨q.rep, inner_self_ne_zero.mpr q.rep_nonzero, h⟩

instance rayT2Space : T2Space (Projectivization ℂ H) := by
  constructor
  intro q r h
  obtain ⟨u, hq, hr⟩ := exists_common_rayChartDomain q r
  let : T2Space (rayChartDomain u) := (rayChartHomeomorph u).isEmbedding.t2Space
  have hqr : (⟨q,hq⟩ : rayChartDomain u) ≠ ⟨r,hr⟩ := fun he => h (congrArg Subtype.val he)
  obtain ⟨U,V,hU,hV,hqU,hrV,hUV⟩ := t2_separation hqr
  have hopen := (isOpen_rayChartDomain u).isOpenMap_subtype_val
  exact ⟨Subtype.val '' U, Subtype.val '' V, hopen _ hU, hopen _ hV,
    ⟨_, hqU, rfl⟩, ⟨_, hrV, rfl⟩, Set.disjoint_image_of_injective Subtype.val_injective hUV⟩

end
end GaussianTesting
