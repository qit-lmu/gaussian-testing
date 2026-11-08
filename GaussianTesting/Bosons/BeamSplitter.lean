module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.ModesC
public import GaussianTesting.Bosons.Mixed
public import GaussianTesting.Bosons.Coherent

@[expose] public section

/-!
# The balanced beam splitter as a substitution operator, and the four-copy test

`U_{π/4}` is implemented with **no operator exponentials**: it is the linear
substitution sending the standard creation monomial of exponents `(p, q)` to
the corresponding monomial in the rotated modes `(1,1)/√2`, `(−1,1)/√2`.
Everything needed about it follows from the word calculus of
`Bosons/ModesC.lean`: the intertwining relation `U ∘ a†_c = a†_{Rc} ∘ U`,
`U vac = vac`, Gram preservation (hence blockwise unitarity), and the inverse
substitution `V` (rotation by `−π/4`).

Main results:

* `QB_eq_conj` — the beam-splitter identity `Q = U (1 ⊗ |0⟩⟨0|) U†`: the
  coherent-state test of `Bosons/Coherent.lean` is the conjugated vacuum test.
* `colF`/`p4B` — the reduced state of `U† ψ⊗²` as an explicit Gram family of
  columns, and the four-copy acceptance probability
  `p4B ψ = tr[P₀ ρ⊗²]` in trace-pairing form.

The manuscript source note for Figure 1(b) specifies the identity for the
second-register phase shift `R` and positive balanced beam splitter `U`:
`(UR)† (N₁ - N₂) (UR) = -Λ`. Its finite-core form and the full physical
equal-count accepting-projection identity are proved in
`Bosons/MeanZeroMeasurement.lean` and its supporting number-basis modules.
-/

namespace GaussianTesting

open Complex Finsupp
open scoped ComplexConjugate ENNReal

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {m : ℕ}

local notation "⟪" x ", " y "⟫_ℂ" => inner ℂ x y

/-! ### The rotated modes and factorial normalisers -/

/-- Standard modes. -/
def stdModes : Fin 2 → Fin 2 → ℂ := ![![1, 0], ![0, 1]]

/-- Rotated modes (unnormalised): images of the standard modes under rotation
by `π/4`, scaled by `√2`. -/
def rotModes : Fin 2 → Fin 2 → ℂ := ![![1, 1], ![-1, 1]]

/-- Inverse-rotated modes (unnormalised). -/
def rotInvModes : Fin 2 → Fin 2 → ℂ := ![![1, -1], ![1, 1]]

/-- `∏_l √(p_l!)` as a complex scalar. -/
noncomputable def nFact (p : Fin m → ℕ) : ℂ :=
  ((∏ l, Real.sqrt (p l).factorial : ℝ) : ℂ)

lemma nFact_ne_zero (p : Fin m → ℕ) : nFact p ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (Finset.prod_pos fun l _ =>
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos (p l)))

private lemma beam_nFact_zero : nFact (0 : Fin m → ℕ) = 1 := by
  simp [nFact]

private lemma beam_nFact_update (p : Fin m → ℕ) (l : Fin m) :
    nFact (Function.update p l (p l + 1)) =
      (Real.sqrt (p l + 1) : ℂ) * nFact p := by
  classical
  unfold nFact
  rw [← Complex.ofReal_mul]
  congr 1
  have he : (fun k => Real.sqrt ((Function.update p l (p l + 1)) k).factorial) =
      fun k => (if k = l then Real.sqrt (p l + 1) else 1) *
        Real.sqrt (p k).factorial := by
    funext k
    by_cases h : k = l
    · subst k
      simp [Nat.factorial_succ]
    · simp [h]
  rw [he, Finset.prod_mul_distrib]
  simp

private lemma beam_copyL_ad (p q : Fin m → ℕ) (l : Fin m) :
    copyL (adF l) (Finsupp.single (p,q) 1) =
      (Real.sqrt (p l + 1) : ℂ) •
        Finsupp.single (Function.update p l (p l + 1), q) 1 := by
  simp [copyL, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

private lemma beam_copyR_ad (p q : Fin m → ℕ) (l : Fin m) :
    copyR (adF l) (Finsupp.single (p,q) 1) =
      (Real.sqrt (q l + 1) : ℂ) •
        Finsupp.single (p, Function.update q l (q l + 1)) 1 := by
  simp [copyR, adF, Finsupp.lsum_single, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

private lemma beam_exp_induction
    (P : (Fin 2 → Fin m → ℕ) → Prop)
    (hz : P 0) (hs : ∀ α s l, P α → P (bump α s l))
    (α : Fin 2 → Fin m → ℕ) : P α := by
  suffices h : ∀ n, ∀ α : Fin 2 → Fin m → ℕ, (∑ s, ∑ l, α s l) = n → P α from
    h _ α rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α hn
    by_cases hzero : α = 0
    · simpa [hzero] using hz
    obtain ⟨s, hs'⟩ := Function.ne_iff.mp hzero
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hs'
    have hb : bump (debump α s l) s l = α := by
      ext t k
      by_cases ht : t = s <;> by_cases hk : k = l <;>
        simp_all [bump, debump, Nat.sub_add_cancel (Nat.pos_of_ne_zero hl)]
    have hd : (∑ t, ∑ k, debump α s l t k) < n := by
      have he : ∀ t k, bump (debump α s l) s l t k =
          debump α s l t k + if t = s ∧ k = l then 1 else 0 := by
        intro t k
        by_cases ht : t = s <;> by_cases hk : k = l <;> simp_all [bump]
      have heq : (∑ t, ∑ k, bump (debump α s l) s l t k) =
          (∑ t, ∑ k, debump α s l t k) + 1 := by
        simp only [he, ite_and, Finset.sum_add_distrib]
        simp [Finset.sum_ite_irrel]
      rw [hb, hn] at heq
      omega
    rw [← hb]
    exact hs _ s l (ih _ hd _ rfl)

/-- The standard monomial is the scaled basis vector:
`(a†₁)^p (a†₂)^q |vac⟩ = (∏√(p!))(∏√(q!)) · single (p,q) 1`. -/
lemma gmonC_stdModes (p q : Fin m → ℕ) :
    gmonC stdModes ![p, q] =
      (nFact p * nFact q) • Finsupp.single ((p, q) :
        (Fin m → ℕ) × (Fin m → ℕ)) (1 : ℂ) := by
  classical
  have h : ∀ α : Fin 2 → Fin m → ℕ,
      gmonC stdModes α =
        (nFact (α 0) * nFact (α 1)) • Finsupp.single (α 0, α 1) 1 := by
    intro α
    induction α using beam_exp_induction with
    | hz =>
      simp only [gmonC_zero, Pi.zero_apply, beam_nFact_zero, mul_one, one_smul]
      rfl
    | hs α t l ih =>
      rw [← gmonC_succ, ih, map_smul]
      fin_cases t
      · simp only [stdModes,
          AdmC, LinearMap.add_apply, LinearMap.smul_apply,
          beam_copyL_ad]
        simp [bump, beam_nFact_update, mul_comm, mul_left_comm, mul_assoc]
      · simp only [stdModes,
          AdmC, LinearMap.add_apply, LinearMap.smul_apply,
          beam_copyR_ad]
        simp [bump, beam_nFact_update, mul_comm, mul_assoc]
  exact h ![p,q]

/-! ### The substitution operators -/

/-- The balanced beam splitter `U_{π/4}` as a substitution operator. -/
noncomputable def Usub (m : ℕ) : FA2 m →ₗ[ℂ] FA2 m :=
  Finsupp.lsum ℂ fun p =>
    LinearMap.toSpanSingleton ℂ _
      (((((Real.sqrt 2 : ℝ) : ℂ) ^ (degB p.1 + degB p.2))⁻¹ *
        (nFact p.1 * nFact p.2)⁻¹) • gmonC rotModes ![p.1, p.2])

/-- The inverse substitution `U_{−π/4}`. -/
noncomputable def Vsub (m : ℕ) : FA2 m →ₗ[ℂ] FA2 m :=
  Finsupp.lsum ℂ fun p =>
    LinearMap.toSpanSingleton ℂ _
      (((((Real.sqrt 2 : ℝ) : ℂ) ^ (degB p.1 + degB p.2))⁻¹ *
        (nFact p.1 * nFact p.2)⁻¹) • gmonC rotInvModes ![p.1, p.2])

@[simp] lemma Usub_vac2 : Usub m (vac2 (m := m)) = vac2 := by
  classical
  have hz : ![(0 : Fin m → ℕ), 0] = (0 : Fin 2 → Fin m → ℕ) := by
    funext i; fin_cases i <;> rfl
  simp only [Usub, vac2, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    one_smul]
  have hg : gmonC (m := m) rotModes ![(fun _ => 0), (fun _ => 0)] = vac2 :=
    hz ▸ gmonC_zero rotModes
  rw [hg]
  simp [nFact, degB, vac2]

@[simp] lemma Vsub_vac2 : Vsub m (vac2 (m := m)) = vac2 := by
  classical
  have hz : ![(0 : Fin m → ℕ), 0] = (0 : Fin 2 → Fin m → ℕ) := by
    funext i; fin_cases i <;> rfl
  simp only [Vsub, vac2, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    one_smul]
  have hg : gmonC (m := m) rotInvModes ![(fun _ => 0), (fun _ => 0)] = vac2 :=
    hz ▸ gmonC_zero rotInvModes
  rw [hg]
  simp [nFact, degB, vac2]

/-- Rotation of mode vectors by `π/4`. -/
noncomputable def rotU (c : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(c 0 - c 1) / (Real.sqrt 2 : ℝ), (c 0 + c 1) / (Real.sqrt 2 : ℝ)]

/-- Rotation of mode vectors by `−π/4`. -/
noncomputable def rotV (c : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(c 0 + c 1) / (Real.sqrt 2 : ℝ), (-c 0 + c 1) / (Real.sqrt 2 : ℝ)]

private noncomputable def beam_coeff (p q : Fin m → ℕ) : ℂ :=
  (((Real.sqrt 2 : ℂ) ^ (degB p + degB q))⁻¹ * (nFact p * nFact q)⁻¹)

private lemma beam_deg_update (p : Fin m → ℕ) (l : Fin m) :
    degB (Function.update p l (p l + 1)) = degB p + 1 := by
  classical
  unfold degB
  have h := Finset.sum_update_of_mem (Finset.mem_univ l) p (p l + 1)
  simp only [Finset.sdiff_singleton_eq_erase] at h
  have he := Finset.sum_erase_add Finset.univ p (Finset.mem_univ l)
  omega

private lemma beam_coeff_L (p q : Fin m → ℕ) (l : Fin m) :
    (Real.sqrt (p l + 1) : ℂ) *
      beam_coeff (Function.update p l (p l + 1)) q =
      (Real.sqrt 2 : ℂ)⁻¹ * beam_coeff p q := by
  have hr : (Real.sqrt (p l + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < p l + 1))
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  simp only [beam_coeff, beam_deg_update, beam_nFact_update]
  rw [show degB p + 1 + degB q = (degB p + degB q) + 1 by omega, pow_succ]
  field_simp

private lemma beam_coeff_R (p q : Fin m → ℕ) (l : Fin m) :
    (Real.sqrt (q l + 1) : ℂ) *
      beam_coeff p (Function.update q l (q l + 1)) =
      (Real.sqrt 2 : ℂ)⁻¹ * beam_coeff p q := by
  have hr : (Real.sqrt (q l + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < q l + 1))
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  simp only [beam_coeff, beam_deg_update, beam_nFact_update]
  rw [show degB p + (degB q + 1) = (degB p + degB q) + 1 by omega, pow_succ]
  field_simp

private lemma beam_bump_L (p q : Fin m → ℕ) (l : Fin m) :
    bump ![p,q] 0 l = ![Function.update p l (p l + 1),q] := by
  ext t k
  fin_cases t <;> simp [bump]

private lemma beam_bump_R (p q : Fin m → ℕ) (l : Fin m) :
    bump ![p,q] 1 l = ![p,Function.update q l (q l + 1)] := by
  ext t k
  fin_cases t <;> simp [bump]

private lemma beam_adm_vec (a b : ℂ) (u v : Fin 2 → ℂ) (l : Fin m) :
    AdmC (a • u + b • v) l = a • AdmC u l + b • AdmC v l := by
  ext f i
  simp [AdmC, add_smul, smul_add, smul_smul]
  ring

private lemma beam_intertwine (T : FA2 m →ₗ[ℂ] FA2 m)
    (X : Fin 2 → Fin 2 → ℂ) (R : (Fin 2 → ℂ) → Fin 2 → ℂ)
    (hT : ∀ p q, T (Finsupp.single (p,q) 1) = beam_coeff p q • gmonC X ![p,q])
    (hR : ∀ c, R c = (c 0 / (Real.sqrt 2 : ℂ)) • X 0 +
      (c 1 / (Real.sqrt 2 : ℂ)) • X 1)
    (c : Fin 2 → ℂ) (l : Fin m) :
    T ∘ₗ AdmC c l = AdmC (R c) l ∘ₗ T := by
  apply Finsupp.lhom_ext
  rintro ⟨p,q⟩ z
  have hz : Finsupp.single (p,q) z = z • Finsupp.single (p,q) 1 := by simp
  simp only [hz, map_smul]
  congr 1
  simp only [LinearMap.comp_apply]
  rw [show AdmC c l (Finsupp.single (p,q) 1) =
      (c 0 * (Real.sqrt (p l + 1) : ℂ)) •
        Finsupp.single (Function.update p l (p l + 1), q) 1 +
      (c 1 * (Real.sqrt (q l + 1) : ℂ)) •
        Finsupp.single (p, Function.update q l (q l + 1)) 1 by
    simp [AdmC, beam_copyL_ad, beam_copyR_ad]]
  rw [map_add, map_smul, map_smul, hT, hT, hT, hR, beam_adm_vec]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_smul,
    gmonC_succ, beam_bump_L, beam_bump_R]
  rw [mul_assoc, beam_coeff_L, mul_assoc, beam_coeff_R]
  simp only [div_eq_mul_inv, mul_assoc, smul_add, smul_smul, mul_comm]

/-- Intertwining: `U ∘ a†_c = a†_{R c} ∘ U`. -/
theorem Usub_admC (c : Fin 2 → ℂ) (l : Fin m) :
    Usub m ∘ₗ AdmC c l = AdmC (rotU c) l ∘ₗ Usub m := by
  apply beam_intertwine (Usub m) rotModes rotU
  · intro p q
    simp [Usub, Finsupp.lsum_single, beam_coeff]
  · intro c
    ext t
    fin_cases t <;> simp [rotU, rotModes, div_eq_mul_inv, sub_eq_add_neg] <;> ring

theorem Vsub_admC (c : Fin 2 → ℂ) (l : Fin m) :
    Vsub m ∘ₗ AdmC c l = AdmC (rotV c) l ∘ₗ Vsub m := by
  apply beam_intertwine (Vsub m) rotInvModes rotV
  · intro p q
    simp [Vsub, Finsupp.lsum_single, beam_coeff]
  · intro c
    ext t
    fin_cases t <;> simp [rotV, rotInvModes, div_eq_mul_inv] <;> ring

private lemma beam_rotUV (c : Fin 2 → ℂ) : rotU (rotV c) = c := by
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  funext i
  fin_cases i <;> simp [rotU, rotV] <;> field_simp <;>
    (first | linear_combination -c 0 * hsq | linear_combination -c 1 * hsq)

private lemma beam_rotVU (c : Fin 2 → ℂ) : rotV (rotU c) = c := by
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  funext i
  fin_cases i <;> simp [rotU, rotV] <;> field_simp <;>
    (first | linear_combination -c 0 * hsq | linear_combination -c 1 * hsq)

private lemma beam_inverse (S T : FA2 m →ₗ[ℂ] FA2 m)
    (R R' : (Fin 2 → ℂ) → Fin 2 → ℂ)
    (hS : S vac2 = vac2) (hT : T vac2 = vac2)
    (hSad : ∀ c l, S ∘ₗ AdmC c l = AdmC (R c) l ∘ₗ S)
    (hTad : ∀ c l, T ∘ₗ AdmC c l = AdmC (R' c) l ∘ₗ T)
    (hR : ∀ c, R (R' c) = c) :
    S ∘ₗ T = LinearMap.id := by
  have hw : ∀ L : List ((Fin 2 → ℂ) × Fin m), S (T (monWC L)) = monWC L := by
    intro L
    induction L with
    | nil => simpa [monWC] using (show S (T vac2) = vac2 by rw [hT, hS])
    | cons x L ih =>
      rw [monWC_cons]
      have ht := LinearMap.congr_fun (hTad x.1 x.2) (monWC L)
      have hs := LinearMap.congr_fun (hSad (R' x.1) x.2) (T (monWC L))
      change T (AdmC x.1 x.2 (monWC L)) = _ at ht
      change S (AdmC (R' x.1) x.2 (T (monWC L))) = _ at hs
      simp only [LinearMap.comp_apply] at ht hs
      rw [ht, hs, hR, ih]
  apply Finsupp.lhom_ext
  rintro ⟨p,q⟩ z
  have h := hw (expWordC stdModes ![p,q])
  change S (T (gmonC stdModes ![p,q])) = gmonC stdModes ![p,q] at h
  rw [gmonC_stdModes, map_smul, map_smul] at h
  have hscalar : nFact p * nFact q ≠ 0 := mul_ne_zero (nFact_ne_zero p) (nFact_ne_zero q)
  have he := (smul_right_injective _ hscalar) h
  change S (T (Finsupp.single (p,q) z)) = Finsupp.single (p,q) z
  have hz : Finsupp.single (p,q) z = z • Finsupp.single (p,q) 1 := by simp
  rw [hz, map_smul, map_smul, he]

/-- The substitutions are mutually inverse. -/
theorem Usub_Vsub (m : ℕ) : Usub m ∘ₗ Vsub m = LinearMap.id := by
  exact beam_inverse (Usub m) (Vsub m) rotU rotV
    Usub_vac2 Vsub_vac2 Usub_admC Vsub_admC beam_rotUV

theorem Vsub_Usub (m : ℕ) : Vsub m ∘ₗ Usub m = LinearMap.id := by
  exact beam_inverse (Vsub m) (Usub m) rotV rotU
    Vsub_vac2 Usub_vac2 Vsub_admC Usub_admC beam_rotVU

private lemma beam_pair_add_left (f f' g : FA2 m) :
    pairF2 (f + f') g = pairF2 f g + pairF2 f' g := by
  classical
  unfold pairF2
  exact Finsupp.sum_add_index (by simp) (by intros; simp [add_mul])

private lemma beam_pair_add_right (f g g' : FA2 m) :
    pairF2 f (g + g') = pairF2 f g + pairF2 f g' := by
  classical
  simp [pairF2, Finsupp.sum, mul_add, Finset.sum_add_distrib]

private lemma beam_pair_smul_left (z : ℂ) (f g : FA2 m) :
    pairF2 (z • f) g = star z * pairF2 f g := by
  classical
  unfold pairF2
  rw [Finsupp.sum_smul_index' (by simp)]
  simp [Finsupp.sum, map_mul, mul_assoc, Finset.mul_sum]

private lemma beam_pair_smul_right (z : ℂ) (f g : FA2 m) :
    pairF2 f (z • g) = z * pairF2 f g := by
  classical
  simp [pairF2, Finsupp.sum, Finset.mul_sum, mul_left_comm]

private lemma beam_fact_sq (p : Fin m → ℕ) :
    (nFact p) ^ 2 = ∏ l, ((p l).factorial : ℂ) := by
  unfold nFact
  rw [← Complex.ofReal_pow, ← Finset.prod_pow]
  push_cast
  apply Finset.prod_congr rfl
  intro l _
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (p l).factorial)

private lemma beam_coeff_gram (p q : Fin m → ℕ) :
    star (beam_coeff p q) * beam_coeff p q *
      ((∏ l, ((p l).factorial : ℂ) * 2 ^ p l) *
        ∏ l, ((q l).factorial : ℂ) * 2 ^ q l) = 1 := by
  have hn : nFact p * nFact q ≠ 0 := mul_ne_zero (nFact_ne_zero p) (nFact_ne_zero q)
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hc : star (beam_coeff p q) = beam_coeff p q := by
    simp [beam_coeff, nFact]
  rw [hc]
  have he : ((∏ l, ((p l).factorial : ℂ) * 2 ^ p l) *
        ∏ l, ((q l).factorial : ℂ) * 2 ^ q l) =
      (nFact p * nFact q)^2 * ((Real.sqrt 2 : ℂ)^(degB p + degB q))^2 := by
    rw [mul_pow, beam_fact_sq, beam_fact_sq, ← pow_mul, mul_comm _ 2, pow_mul, hs,
      pow_add]
    simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, degB]
    ring
  rw [he]
  unfold beam_coeff
  field_simp
  exact div_self hn

private lemma beam_pair_substitution (T : FA2 m →ₗ[ℂ] FA2 m)
    (X : Fin 2 → Fin 2 → ℂ)
    (hT : ∀ p q, T (Finsupp.single (p,q) 1) = beam_coeff p q • gmonC X ![p,q])
    (hdiag : ∀ s t, pairH (X s) (X t) = if s = t then 2 else 0)
    (f g : FA2 m) : pairF2 (T f) (T g) = pairF2 f g := by
  classical
  have hsingle (p q p' q' : Fin m → ℕ) :
      pairF2 (T (Finsupp.single (p,q) 1)) (T (Finsupp.single (p',q') 1)) =
        pairF2 (Finsupp.single (p,q) 1) (Finsupp.single (p',q') 1) := by
    rw [hT, hT, beam_pair_smul_left, beam_pair_smul_right, gram_diagC]
    · have he : (![p,q] : Fin 2 → Fin m → ℕ) = ![p',q'] ↔ (p,q) = (p',q') := by
        constructor
        · intro h; exact Prod.ext (congrFun h 0) (congrFun h 1)
        · intro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl
      simp only [he]
      by_cases hp : (p,q) = (p',q')
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        simp only [ite_true, Fin.prod_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one, hdiag]
        have hc := beam_coeff_gram p q
        simpa [pairF2, mul_assoc, mul_left_comm, mul_comm] using hc
      · simp [hp, pairF2, Finsupp.single_apply, eq_comm]
    · intro s t hst _ _
      simp [hdiag, hst]
  induction f using Finsupp.induction_linear with
  | zero => simp [pairF2]
  | add f f' hf hf' => simp [beam_pair_add_left, hf, hf']
  | single pq z =>
    induction g using Finsupp.induction_linear with
    | zero => simp [pairF2]
    | add g g' hg hg' => simp [beam_pair_add_right, hg, hg']
    | single pq' w =>
      have hz : Finsupp.single pq z = z • Finsupp.single pq 1 := by simp
      have hw : Finsupp.single pq' w = w • Finsupp.single pq' 1 := by simp
      rw [hz, hw, map_smul, map_smul, beam_pair_smul_left, beam_pair_smul_right,
        beam_pair_smul_left, beam_pair_smul_right, hsingle pq.1 pq.2 pq'.1 pq'.2]

/-- Gram preservation: the substitution preserves the pairing. -/
theorem pairF2_Usub (f g : FA2 m) :
    pairF2 (Usub m f) (Usub m g) = pairF2 f g := by
  apply beam_pair_substitution (Usub m) rotModes
  · intro p q
    simp [Usub, Finsupp.lsum_single, beam_coeff]
  · intro s t
    fin_cases s <;> fin_cases t <;> norm_num [pairH, rotModes, Fin.sum_univ_two]

theorem pairF2_Vsub (f g : FA2 m) :
    pairF2 (Vsub m f) (Vsub m g) = pairF2 f g := by
  apply beam_pair_substitution (Vsub m) rotInvModes
  · intro p q
    simp [Vsub, Finsupp.lsum_single, beam_coeff]
  · intro s t
    fin_cases s <;> fin_cases t <;> norm_num [pairH, rotInvModes, Fin.sum_univ_two]

lemma conservesDeg2_Usub (m : ℕ) : ConservesDeg2 (Usub m) := by
  classical
  intro p q hq
  have hs : q ∈ (gmonC rotModes ![p.1, p.2]).support := by
    simp only [Usub, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
      one_smul] at hq
    exact Finsupp.support_smul hq
  simpa [Fin.sum_univ_two, degB2] using
    gmonC_homog rotModes ![p.1, p.2] q hs

lemma conservesDeg2_Vsub (m : ℕ) : ConservesDeg2 (Vsub m) := by
  classical
  intro p q hq
  have hs : q ∈ (gmonC rotInvModes ![p.1, p.2]).support := by
    simp only [Vsub, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
      one_smul] at hq
    exact Finsupp.support_smul hq
  simpa [Fin.sum_univ_two, degB2] using
    gmonC_homog rotInvModes ![p.1, p.2] q hs

/-! ### The ℓ²-level beam splitter -/

private lemma beam_lift_homog (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    IsHomog2 n (blockLift2 n v) := by
  intro i hi
  by_contra h
  have hz : blockLift2 n v i = 0 := by simp [blockLift2_apply, h]
  exact (Finsupp.mem_support_iff.mp hi) hz

private lemma beam_lift_block (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    homogToBlock2 n (blockLift2 n v) = v := by
  ext i
  change blockLift2 n v i.1 = v i
  simp [blockLift2_apply, i.2]

private lemma beam_block_inner (T : FA2 m →ₗ[ℂ] FA2 m)
    (hT : ConservesDeg2 T) (hpair : ∀ f g, pairF2 (T f) (T g) = pairF2 f g)
    (n : ℕ) (v w : BlockSp (degB2 (m := m)) n) :
    ⟪toBlock2 T n v, toBlock2 T n w⟫_ℂ = ⟪v, w⟫_ℂ := by
  have hTv : IsHomog2 n (T (blockLift2 n v)) := by
    rw [← blockLift2_toBlock2 hT]
    exact beam_lift_homog _ _
  rw [← beam_lift_block n v, ← beam_lift_block n w,
    toBlock2_homogToBlock2 hT (beam_lift_homog _ _),
    toBlock2_homogToBlock2 hT (beam_lift_homog _ _),
    inner_homogToBlock2 hTv, hpair,
    ← inner_homogToBlock2 (beam_lift_homog n v), beam_lift_block, beam_lift_block]

private lemma beam_block_norm (T : FA2 m →ₗ[ℂ] FA2 m)
    (hT : ConservesDeg2 T) (hpair : ∀ f g, pairF2 (T f) (T g) = pairF2 f g)
    (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    ‖toBlock2 T n v‖ = ‖v‖ := by
  have h := congrArg Complex.re (beam_block_inner T hT hpair n v v)
  simp only [inner_self_eq_norm_sq_to_K] at h
  simp only [← RCLike.ofReal_pow] at h
  change (↑(‖toBlock2 T n v‖ ^ 2) : ℂ).re = (↑(‖v‖ ^ 2) : ℂ).re at h
  simp only [Complex.ofReal_re] at h
  nlinarith [norm_nonneg (toBlock2 T n v), norm_nonneg v]

/-- The beam splitter on ℓ², assembled blockwise. -/
lemma toBlock2_Usub_norm (m n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    ‖toBlock2 (Usub m) n v‖ ≤ ‖v‖ := by
  exact (beam_block_norm (Usub m) (conservesDeg2_Usub m)
    (fun f g => pairF2_Usub f g) n v).le

lemma toBlock2_Vsub_norm (m n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    ‖toBlock2 (Vsub m) n v‖ ≤ ‖v‖ := by
  exact (beam_block_norm (Vsub m) (conservesDeg2_Vsub m)
    (fun f g => pairF2_Vsub f g) n v).le

noncomputable def ULp (m : ℕ) :
    lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 →L[ℂ]
      lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 :=
  blockOp (degB2 (m := m))
    (fun n => LinearMap.mkContinuous (toBlock2 (Usub m) n) 1
      (fun v => by simpa using toBlock2_Usub_norm m n v))
    (fun n v => toBlock2_Usub_norm m n v)

noncomputable def VLp (m : ℕ) :
    lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 →L[ℂ]
      lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 :=
  blockOp (degB2 (m := m))
    (fun n => LinearMap.mkContinuous (toBlock2 (Vsub m) n) 1
      (fun v => by simpa using toBlock2_Vsub_norm m n v))
    (fun n v => toBlock2_Vsub_norm m n v)

private lemma beam_U_blocks (f : L2 ((Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB2 (ULp m f) n = toBlock2 (Usub m) n (blockProj degB2 f n) := by
  ext i
  have hi := blockOp_apply (degB2 (m := m))
    (fun k => LinearMap.mkContinuous (toBlock2 (Usub m) k) 1
      (fun v => by simpa using toBlock2_Usub_norm m k v))
    (fun k v => toBlock2_Usub_norm m k v) f i.1
  change ULp m f i.1 = _
  unfold ULp at *
  rcases i with ⟨i, hi_deg⟩
  subst n
  exact hi

private lemma beam_V_blocks (f : L2 ((Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB2 (VLp m f) n = toBlock2 (Vsub m) n (blockProj degB2 f n) := by
  ext i
  have hi := blockOp_apply (degB2 (m := m))
    (fun k => LinearMap.mkContinuous (toBlock2 (Vsub m) k) 1
      (fun v => by simpa using toBlock2_Vsub_norm m k v))
    (fun k v => toBlock2_Vsub_norm m k v) f i.1
  change VLp m f i.1 = _
  unfold VLp at *
  rcases i with ⟨i, hi_deg⟩
  subst n
  exact hi

private lemma beam_block_id (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    toBlock2 (LinearMap.id : FA2 m →ₗ[ℂ] FA2 m) n v = v := by
  ext i
  change blockLift2 n v i.1 = v i
  simp [blockLift2_apply, i.2]

lemma ULp_VLp (m : ℕ) : (ULp m).comp (VLp m) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  have h := congrArg (fun v : BlockSp (degB2 (m := m)) (degB2 i) =>
    v ⟨i, rfl⟩) (show
      blockProj degB2 (ULp m (VLp m f)) (degB2 i) =
        blockProj degB2 f (degB2 i) from by
    rw [beam_U_blocks, beam_V_blocks]
    change (toBlock2 (Usub m) _ ∘ₗ toBlock2 (Vsub m) _) _ = _
    rw [← toBlock2_comp (conservesDeg2_Usub m) (conservesDeg2_Vsub m),
      Usub_Vsub, beam_block_id])
  exact h

lemma VLp_ULp (m : ℕ) : (VLp m).comp (ULp m) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  have h := congrArg (fun v : BlockSp (degB2 (m := m)) (degB2 i) =>
    v ⟨i, rfl⟩) (show
      blockProj degB2 (VLp m (ULp m f)) (degB2 i) =
        blockProj degB2 f (degB2 i) from by
    rw [beam_V_blocks, beam_U_blocks]
    change (toBlock2 (Vsub m) _ ∘ₗ toBlock2 (Usub m) _) _ = _
    rw [← toBlock2_comp (conservesDeg2_Vsub m) (conservesDeg2_Usub m),
      Vsub_Usub, beam_block_id])
  exact h

lemma inner_ULp (f g : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2) :
    ⟪ULp m f, ULp m g⟫_ℂ = ⟪f, g⟫_ℂ := by
  rw [inner_blocks degB2, inner_blocks degB2]
  apply tsum_congr
  intro n
  rw [beam_U_blocks, beam_U_blocks]
  exact beam_block_inner (Usub m) (conservesDeg2_Usub m)
    (fun f g => pairF2_Usub f g) n _ _

lemma norm_ULp (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2) :
    ‖ULp m f‖ = ‖f‖ := by
  have h := congrArg Complex.re (inner_ULp f f)
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
  have hf := norm_nonneg f
  have hu := norm_nonneg (ULp m f)
  change ‖ULp m f‖ ^ 2 = ‖f‖ ^ 2 at h
  nlinarith

lemma norm_VLp (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2) :
    ‖VLp m f‖ = ‖f‖ := by
  have h := congrArg (fun T => T f) (ULp_VLp m)
  change ULp m (VLp m f) = f at h
  exact (norm_ULp (VLp m f)).symm.trans (congrArg norm h)

/-- Adjoint relation: `U† = V`. -/
lemma inner_ULp_left (f g : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2) :
    ⟪ULp m f, g⟫_ℂ = ⟪f, VLp m g⟫_ℂ := by
  have h := congrArg (fun T => T g) (ULp_VLp m)
  change ULp m (VLp m g) = g at h
  calc
    _ = ⟪ULp m f, ULp m (VLp m g)⟫_ℂ := by rw [h]
    _ = _ := inner_ULp _ _

/-! ### The conjugated vacuum test -/

/-- `1 ⊗ |0⟩⟨0|` on ℓ² of two copies. -/
noncomputable def vacProj (m : ℕ) :
    lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 →L[ℂ]
      lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2 := by
  refine LinearMap.mkContinuous
    { toFun := fun f => ⟨fun p => if p.2 = (fun _ => 0) then f (p.1, fun _ => 0) else 0, ?_⟩
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · apply (lp.memℓp f).mono'
    intro p
    split_ifs with h
    · simpa only [← h, Prod.mk.eta] using (le_refl ‖f p‖)
    · simp
  · intro f g
    apply lp.ext
    funext p
    simp only [lp.coeFn_add, Pi.add_apply]
    change (if p.2 = (fun _ => 0) then _ else 0) =
      (if p.2 = (fun _ => 0) then _ else 0) +
      (if p.2 = (fun _ => 0) then _ else 0)
    split_ifs <;> simp
  · intro z f
    apply lp.ext
    funext p
    change (if _ then _ else _) = _
    split_ifs <;> simp_all [Pi.smul_apply]
  · intro f
    simp only [one_mul]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro p
    change ‖if p.2 = (fun _ => 0) then f (p.1, fun _ => 0) else 0‖ ≤ ‖f p‖
    split_ifs with h
    · simpa only [← h, Prod.mk.eta] using (le_refl ‖f p‖)
    · simp

@[simp] lemma vacProj_apply (f : lp (fun _ : (Fin m → ℕ) × (Fin m → ℕ) => ℂ) 2)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    vacProj m f p = if p.2 = (fun _ => 0) then f (p.1, fun _ => 0) else 0 := rfl

private lemma beam_rot_pair (s t : Fin 2) :
    pairH (rotModes s) (rotModes t) = if s = t then 2 else 0 := by
  fin_cases s <;> fin_cases t <;> norm_num [pairH, rotModes, Fin.sum_univ_two]

private lemma beam_MB_gmon (α : Fin 2 → Fin m → ℕ) :
    MB m (gmonC rotModes α) = (2 * (degB (α 1) : ℂ)) • gmonC rotModes α := by
  classical
  have hmode (l : Fin m) :
      adM2 l ∘ₗ aM2 l = AdmC (rotModes 1) l ∘ₗ AmC (rotModes 1) l := by
    ext f i
    simp [adM2, aM2, AdmC, AmC, rotModes]
    ring
  have hterm (l : Fin m) :
      (adM2 l ∘ₗ aM2 l) (gmonC rotModes α) =
        (2 * (α 1 l : ℂ)) • gmonC rotModes α := by
    rw [hmode]
    simp only [LinearMap.comp_apply]
    rw [AmC_gmonC rotModes α 1 (by intro t ht _; simp [beam_rot_pair, Ne.symm ht])]
    simp only [beam_rot_pair, ite_true, map_smul, gmonC_succ]
    by_cases h : α 1 l = 0
    · simp [h]
    · have hb : bump (debump α 1 l) 1 l = α := by
        ext t k
        by_cases ht : t = 1 <;> by_cases hk : k = l <;>
          simp_all [bump, debump, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
      rw [hb, mul_comm]
  simp only [MB, LinearMap.sum_apply, hterm, ← Finset.sum_smul, ← Finset.mul_sum]
  congr 2
  simp [degB]

private noncomputable def beam_e (n : ℕ) (i : {i // degB2 (m := m) i = n}) :
    BlockSp (degB2 (m := m)) n :=
  homogToBlock2 n (Finsupp.single i.1 1)

private lemma beam_e_apply (n : ℕ) (i j : {i // degB2 (m := m) i = n}) :
    beam_e n i j = if i = j then 1 else 0 := by
  classical
  change (Finsupp.single i.1 (1 : ℂ)) j.1 = _
  simp only [Finsupp.single_apply]
  congr 1
  exact propext ⟨Subtype.ext, congrArg Subtype.val⟩

private lemma beam_basis_sum (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    v = ∑ i, v i • beam_e n i := by
  classical
  ext j
  simp [WithLp.ofLp_sum, beam_e_apply, Finset.sum_apply]

private lemma beam_UBVB (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    toBlock2 (Usub m) n (toBlock2 (Vsub m) n v) = v := by
  change (toBlock2 (Usub m) n ∘ₗ toBlock2 (Vsub m) n) v = v
  rw [← toBlock2_comp (conservesDeg2_Usub m) (conservesDeg2_Vsub m),
    Usub_Vsub, beam_block_id]

private lemma beam_VBUB (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    toBlock2 (Vsub m) n (toBlock2 (Usub m) n v) = v := by
  change (toBlock2 (Vsub m) n ∘ₗ toBlock2 (Usub m) n) v = v
  rw [← toBlock2_comp (conservesDeg2_Vsub m) (conservesDeg2_Usub m),
    Vsub_Usub, beam_block_id]

private lemma beam_UB_eigen (n : ℕ) (i : {i // degB2 (m := m) i = n}) :
    mBlock m n (toBlock2 (Usub m) n (beam_e n i)) =
      (2 * (degB i.1.2 : ℂ)) • toBlock2 (Usub m) n (beam_e n i) := by
  classical
  have hi : IsHomog2 n (Finsupp.single i.1 1) := by
    intro j hj
    have he := (Finsupp.mem_support_single _ _ _).mp hj
    simpa [← he.1] using i.2
  have hu : IsHomog2 n (Usub m (Finsupp.single i.1 1)) := by
    intro j hj
    exact (conservesDeg2_Usub m i.1 j hj).trans i.2
  rw [beam_e, toBlock2_homogToBlock2 (conservesDeg2_Usub m) hi,
    mBlock, toBlock2_homogToBlock2 (conservesDeg2_MB m) hu]
  simp only [Usub, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul,
    map_smul, beam_MB_gmon]
  ext j
  simp [homogToBlock2, smul_smul, mul_left_comm]
  ring

private noncomputable def beam_P (n : ℕ)
    (v : BlockSp (degB2 (m := m)) n) : BlockSp (degB2 (m := m)) n :=
  WithLp.toLp 2 (fun i => if i.1.2 = 0 then v i else 0)

private lemma beam_ker_coord (n : ℕ) (w : BlockSp (degB2 (m := m)) n)
    (hw : w ∈ LinearMap.ker (mBlock m n))
    (i : {i // degB2 (m := m) i = n}) (hi : i.1.2 ≠ 0) :
    toBlock2 (Vsub m) n w i = 0 := by
  classical
  have hd : degB i.1.2 ≠ 0 := by
    intro h
    apply hi
    funext l
    exact (Finset.sum_eq_zero_iff.mp h) l (Finset.mem_univ l)
  have hl : (2 * (degB i.1.2 : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hd)
  have h := mBlock_isSymmetric m n (toBlock2 (Usub m) n (beam_e n i)) w
  rw [beam_UB_eigen, LinearMap.mem_ker.mp hw, inner_zero_right,
    inner_smul_left] at h
  have hz : ⟪toBlock2 (Usub m) n (beam_e n i), w⟫_ℂ = 0 := by
    exact (mul_eq_zero.mp h).resolve_left (by simpa using hl)
  rw [← beam_UBVB n w,
    beam_block_inner (Usub m) (conservesDeg2_Usub m) (fun f g => pairF2_Usub f g)] at hz
  simpa [PiLp.inner_apply, beam_e_apply, mul_ite, ite_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq] using hz

private lemma beam_block_projection (n : ℕ) (v : BlockSp (degB2 (m := m)) n) :
    (LinearMap.ker (mBlock m n)).starProjection v =
      toBlock2 (Usub m) n (beam_P n (toBlock2 (Vsub m) n v)) := by
  classical
  apply (LinearMap.ker (mBlock m n)).eq_starProjection_of_mem_of_inner_eq_zero
  · rw [LinearMap.mem_ker]
    rw [beam_basis_sum n (beam_P n (toBlock2 (Vsub m) n v))]
    simp only [map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro i _
    change (if i.1.2 = 0 then toBlock2 (Vsub m) n v i else 0) •
      mBlock m n (toBlock2 (Usub m) n (beam_e n i)) = 0
    split_ifs with hi
    · rw [beam_UB_eigen, hi]
      simp [degB]
    · simp
  · intro w hw
    have hv := beam_UBVB n v
    have hw' := beam_UBVB n w
    conv_lhs => rw [← hv]
    rw [← map_sub,
      ← hw', beam_block_inner (Usub m) (conservesDeg2_Usub m)
        (fun f g => pairF2_Usub f g)]
    simp only [beam_VBUB]
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.1.2 = 0
    · simp [beam_P, hi]
    · simp [beam_ker_coord n w hw i hi]

private lemma beam_vac_blocks (f : L2 ((Fin m → ℕ) × (Fin m → ℕ))) (n : ℕ) :
    blockProj degB2 (vacProj m f) n = beam_P n (blockProj degB2 f n) := by
  ext i
  change (if i.1.2 = (fun _ => 0) then f (i.1.1, fun _ => 0) else 0) =
    if i.1.2 = 0 then f i.1 else 0
  have hz : (fun _ : Fin m => (0 : ℕ)) = (0 : Fin m → ℕ) := rfl
  simp only [hz]
  by_cases h : i.1.2 = 0
  · simp only [h, ite_true]
    exact congrArg f (Prod.ext (rfl : i.1.1 = i.1.1) h.symm)
  · simp only [h, ite_false]

/-- **The beam-splitter identity** used for the coherent test of Proposition 6.3:
the model's coherent-state acceptance projection is the conjugated
vacuum test, `Q = U_{π/4} (1 ⊗ |0⟩⟨0|) U_{π/4}†`. -/
theorem QB_eq_conj (m : ℕ) :
    QB m = (ULp m).comp ((vacProj m).comp (VLp m)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext i
  have hq := blockOp_apply (degB2 (m := m))
    (fun n => ((LinearMap.ker (mBlock m n)).starProjection :
      BlockSp (degB2 (m := m)) n →L[ℂ] BlockSp (degB2 (m := m)) n))
    (fun n v => (LinearMap.ker (mBlock m n)).norm_starProjection_apply_le v) f i
  change QB m f i = ULp m (vacProj m (VLp m f)) i
  rw [show QB m f i =
      (LinearMap.ker (mBlock m (degB2 i))).starProjection
        (blockProj degB2 f (degB2 i)) ⟨i,rfl⟩ from hq,
    beam_block_projection]
  have h := beam_U_blocks (vacProj m (VLp m f)) (degB2 i)
  rw [beam_vac_blocks, beam_V_blocks] at h
  exact (congrArg (fun v : BlockSp (degB2 (m := m)) (degB2 i) => v ⟨i,rfl⟩) h).symm

/-! ### Columns of a bipartite vector and the four-copy test -/

variable {κ κ' : Type*}

/-- The `k`-th column of a bipartite ℓ² vector. -/
noncomputable def colF (F : L2 (κ × κ')) (k : κ) : L2 κ' := by
  refine ⟨fun j => F (k, j), mem_of_summable_normSq ?_⟩
  exact (summable_normSq F).comp_injective
    (fun j j' h => by simpa using congrArg Prod.snd h)

@[simp] lemma colF_apply (F : L2 (κ × κ')) (k : κ) (j : κ') :
    colF F k j = F (k, j) := rfl

private lemma beam_norm_sq {ι : Type*} (f : L2 ι) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num) f
  simpa only [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] using h

lemma colF_gramFam (F : L2 (κ × κ')) : GramFam (colF F) := by
  unfold GramFam
  simp_rw [beam_norm_sq, colF_apply]
  exact ((summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp
    (summable_normSq F)).2

lemma colF_total (F : L2 (κ × κ')) : ∑' k, ‖colF F k‖ ^ 2 = ‖F‖ ^ 2 := by
  simp_rw [beam_norm_sq, colF_apply]
  exact (summable_normSq F).tsum_prod.symm

/-- The elementary tensor of the `lpTensorSquare` structure is `tpPair`. -/
lemma lpTensorSquare_tp_eq (ψ φ : L2 κ) :
    (lpTensorSquare κ).tp ψ φ = tpPair ψ φ := by
  rfl

/-- The reduced state (on the second copy) of `U† ψ⊗²`, as a Gram family. -/
noncomputable def redFam (m : ℕ) (ψ : FockB m) : (Fin m → ℕ) → FockB m :=
  colF (VLp m (tpPair ψ ψ))

lemma redFam_gramFam (ψ : FockB m) : GramFam (redFam m ψ) :=
  colF_gramFam _

/-- The model's four-copy acceptance quantity, defined by the reduced trace pairing
`p₄(ψ) = tr[P₀ ρ⊗²]` with `ρ = tr₁[U† ψ⊗² U]`.
The physical four-copy projection and its reduced-trace identity are constructed
in `SchrodingerFourCopy.lean`. -/
noncomputable def p4B (m : ℕ) (ψ : FockB m) : ℝ :=
  trPair (P0B m) (tensorFam (redFam m ψ) (redFam m ψ))

/-- The total mass of the reduced family is `1` for unit states. -/
lemma redFam_total {ψ : FockB m} (hψ : ‖ψ‖ = 1) :
    ∑' k, ‖redFam m ψ k‖ ^ 2 = 1 := by
  simp only [redFam, colF_total, norm_VLp, norm_tpPair, hψ, one_mul, one_pow]

end GaussianTesting
