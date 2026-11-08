module

public import GaussianTesting.GradientFlow.Continuation

@[expose] public section

/-! # Gluing the maximal forward solution in Lemma 3.1

Local uniqueness identifies all solutions starting at the same unit vector on
their overlaps. If their union had a finite upper endpoint, the finite-time
energy estimate would extend the solution past that endpoint.
-/

namespace GaussianTesting
open Set Filter
open scoped Topology

/-- Local solutions starting at `x` glue to a maximal forward solution by
uniqueness. If every finite forward endpoint permits an extension, this
solution is defined on the whole nonnegative half-line. -/
theorem exists_global_of_finite_extension {E : Type*} (Q : (ℝ → E) → Set ℝ → Prop) (x : E)
    (hstart : ∃ b > (0 : ℝ), ∃ γ : ℝ → E, γ 0 = x ∧ Q γ (Ico 0 b))
    (huniq : ∀ {η ζ : ℝ → E} {b c t : ℝ}, Q η (Ico 0 b) → Q ζ (Ico 0 c) →
      Icc 0 t ⊆ Ico 0 b → Icc 0 t ⊆ Ico 0 c → η 0 = ζ 0 → EqOn η ζ (Icc 0 t))
    (hlocal : ∀ {γ : ℝ → E} {D : Set ℝ},
      (∀ t ∈ D, ∃ b : ℝ, t ∈ Ico 0 b ∧ Ico 0 b ∈ 𝓝[D] t ∧
        ∃ η : ℝ → E, Q η (Ico 0 b) ∧ EqOn γ η (Ico 0 b)) → Q γ D)
    (hext : ∀ {b : ℝ} {η : ℝ → E}, 0 < b → Q η (Ico 0 b) →
      ∃ c > b, ∃ ζ : ℝ → E, EqOn η ζ (Ico 0 b) ∧ Q ζ (Ico 0 c)) :
    ∃ γ : ℝ → E, γ 0 = x ∧ Q γ (Ici 0) := by
  classical
  let R : Set ℝ := {b | 0 < b ∧ ∃ η : ℝ → E, η 0 = x ∧ Q η (Ico 0 b)}
  obtain ⟨δ, hδ, η, hη0, hη⟩ := hstart
  have hδR : δ ∈ R := ⟨hδ, η, hη0, hη⟩
  have hR : R.Nonempty := ⟨δ, hδR⟩
  -- Select a local solution for each reachable endpoint.
  let seg (b : ℝ) (hb : b ∈ R) := Classical.choose hb.2
  have seg_spec (b : ℝ) (hb : b ∈ R) :
      seg b hb 0 = x ∧ Q (seg b hb) (Ico 0 b) :=
    Classical.choose_spec hb.2
  let D : Set ℝ := {t | 0 ≤ t ∧ ∃ b ∈ R, t < b}
  let γ (t : ℝ) := if ht : t ∈ D then
    seg (Classical.choose ht.2) (Classical.choose_spec ht.2).1 t else x
  have agrees (b : ℝ) (hb : b ∈ R) : EqOn γ (seg b hb) (Ico 0 b) := by
    intro t ht
    have htD : t ∈ D := ⟨ht.1, b, hb, ht.2⟩
    let c := Classical.choose htD.2
    have hc : c ∈ R ∧ t < c := Classical.choose_spec htD.2
    simp only [γ, dite_eq_left htD]
    have heq := huniq (seg_spec c hc.1).2 (seg_spec b hb).2
      (Icc_subset_Ico_right hc.2) (Icc_subset_Ico_right ht.2)
      ((seg_spec c hc.1).1.trans (seg_spec b hb).1.symm)
    exact heq (right_mem_Icc.mpr ht.1)
  have hγ0 : γ 0 = x := (agrees δ hδR (left_mem_Ico.mpr hδ)).trans (seg_spec δ hδR).1
  have sol : Q γ D := by
    apply hlocal
    rintro t ⟨ht₀, b, hb, htb⟩
    have hnear : Ico 0 b ∈ 𝓝[D] t := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htb)]
        with u hu hub using ⟨hu.1, hub⟩
    exact ⟨b, ⟨ht₀, htb⟩, hnear, seg b hb, (seg_spec b hb).2, agrees b hb⟩
  have hunbdd : ¬ BddAbove R := by
    intro hbdd
    let b := sSup R
    have hb : 0 < b := hδ.trans_le (le_csSup hbdd hδR)
    have hD : D = Ico 0 b := by
      ext t
      constructor
      · rintro ⟨ht, c, hc, htc⟩
        exact ⟨ht, htc.trans_le (le_csSup hbdd hc)⟩
      · rintro ⟨ht, htb⟩
        exact ⟨ht, exists_lt_of_lt_csSup hR htb⟩
    have hleft : Q γ (Ico 0 b) := hD ▸ sol
    obtain ⟨c, hc, ζ, hζ, hflow⟩ := hext hb hleft
    have hcR : c ∈ R := ⟨hb.trans hc, ζ, (hζ (left_mem_Ico.mpr hb)).symm.trans hγ0,
      hflow⟩
    exact (not_lt_of_ge (le_csSup hbdd hcR)) hc
  have hD : D = Ici 0 := by
    ext t
    constructor
    · exact fun ht => ht.1
    · intro ht
      exact ⟨ht, not_bddAbove_iff.mp hunbdd t⟩
  exact ⟨γ, hγ0, hD ▸ sol⟩

namespace TensorSquare

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {T : TensorSquare H K} {P : K →L[ℂ] K}

/-- A finite maximal endpoint is impossible: the energy estimate gives a limit
and local existence extends the trajectory past it. -/
theorem exists_global_unitFlow_by_continuation
    (hP : T.IsAcceptance P) {x : H} (hx : ‖x‖ = 1) :
    ∃ γ : ℝ → H, γ 0 = x ∧ T.IsUnitFlowOn P γ (Ici 0) := by
  apply exists_global_of_finite_extension (T.IsUnitFlowOn P) x
  · obtain ⟨δ, hδ, hseg⟩ := T.exists_smooth_local_unitFlow hP
    obtain ⟨η, hη0, hη, _⟩ := hseg x hx
    exact ⟨δ, hδ, η, hη0, hη.mono Ico_subset_Icc_self⟩
  · exact fun hη hζ h₁ h₂ h₀ => hη.eqOn_Icc hζ hP h₁ h₂ h₀
  · intro γ D h
    constructor
    · intro t ht
      obtain ⟨b, htb, _, η, hη, he⟩ := h t ht
      rw [he htb]
      exact hη.sphere t htb
    · intro t ht
      obtain ⟨b, htb, hnear, η, hη, he⟩ := h t ht
      rw [he htb]
      exact ((hη.deriv t htb).congr he (he htb)).mono_of_mem_nhdsWithin hnear
  · intro b η hb hη
    obtain ⟨c, hc, ζ, he, hζ⟩ := hη.exists_extension_Ico hP hb
    exact ⟨c, hc, ζ, he, hζ.mono Ico_subset_Icc_self⟩

end TensorSquare
end GaussianTesting
