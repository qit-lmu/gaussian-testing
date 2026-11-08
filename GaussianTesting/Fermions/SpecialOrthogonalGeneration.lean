module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.PlaneRotations

@[expose] public section

/-!
# Coordinate-plane generation of the special orthogonal group

Successive plane rotations eliminate a unit column while preserving previously
fixed coordinates. Induction leaves a one-dimensional restriction, on which
determinant one forces the identity. The resulting induction principle is
used to lift SO(2m) rotations to fermionic Gaussian implementers.
-/

namespace GaussianTesting

noncomputable section

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coordinate-plane rotation as an element of the special orthogonal group. -/
def coordinatePlaneRotation (a b : ι) (p q : ℝ) (hab : a ≠ b) (hpq : p ^ 2 + q ^ 2 = 1) :
    Matrix.specialOrthogonalGroup ι ℝ := ⟨planeRotationMatrix a b p q, planeRotationMatrix_mem hab hpq⟩

private lemma choose_plane_parameters (x y : ℝ) :
    ∃ p q : ℝ, p ^ 2 + q ^ 2 = 1 ∧ 0 ≤ p * x + q * y ∧ -q * x + p * y = 0 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · refine ⟨1, 0, by norm_num, ?_, ?_⟩ <;> simp <;> nlinarith [sq_nonneg x, sq_nonneg y]
  · have hs : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    let r := Real.sqrt (x ^ 2 + y ^ 2)
    have hr : 0 < r := Real.sqrt_pos.mpr hs
    have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt hs.le
    refine ⟨x / r, y / r, ?_, ?_, ?_⟩
    · field_simp
      nlinarith
    · have : x / r * x + y / r * y = (x ^ 2 + y ^ 2) / r := by ring
      rw [this]; positivity
    · ring

private lemma reduce_coordinates (G : Subgroup (Matrix.specialOrthogonalGroup ι ℝ))
    (hplane : ∀ a b p q hab hpq, coordinatePlaneRotation a b p q hab hpq ∈ G)
    (s : Finset ι) (a : ι) (ha : a ∉ s) (v : ι → ℝ) (hva : 0 ≤ v a) :
    ∃ M : Matrix.specialOrthogonalGroup ι ℝ, M ∈ G ∧
      0 ≤ M.val.mulVec v a ∧
      (∀ j ∈ s, M.val.mulVec v j = 0) ∧
      (∀ j ∉ insert a s, ∀ w : ι → ℝ, M.val.mulVec w j = w j) := by
  induction s using Finset.induction_on generalizing v with
  | empty =>
    refine ⟨1, G.one_mem, ?_, ?_, ?_⟩
    · simpa using hva
    · simp
    · intro j hj w; simp
  | @insert b s hb ih =>
    have hab : a ≠ b := by simpa using (by simpa only [Finset.mem_insert, not_or] using ha : a ≠ b ∧ a ∉ s).1
    have has : a ∉ s := (by simpa only [Finset.mem_insert, not_or] using ha : a ≠ b ∧ a ∉ s).2
    obtain ⟨p, q, hpq, hnonneg, hzero⟩ := choose_plane_parameters (v a) (v b)
    let A := coordinatePlaneRotation a b p q hab hpq
    have hAa : 0 ≤ A.val.mulVec v a := by
      simpa [A, coordinatePlaneRotation, planeRotationMatrix_mulVec_a hab] using hnonneg
    have hAb : A.val.mulVec v b = 0 := by
      simpa [A, coordinatePlaneRotation, planeRotationMatrix_mulVec_b hab] using hzero
    obtain ⟨M, hM, hMa, hMz, hMfix⟩ := ih has (A.val.mulVec v) hAa
    refine ⟨M * A, G.mul_mem hM (hplane a b p q hab hpq), ?_, ?_, ?_⟩
    · simpa only [Submonoid.coe_mul, ← mulVec_mulVec] using hMa
    · intro j hj
      rw [Submonoid.coe_mul, ← mulVec_mulVec]
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        rw [hMfix b (by simp [hab.symm, hb]), hAb]
      · exact hMz j hj
    · intro j hj w
      have hj' : j ≠ a ∧ j ≠ b ∧ j ∉ s := by
        simpa only [Finset.mem_insert, not_or] using hj
      obtain ⟨hja, hjb, hjs⟩ := hj'
      rw [Submonoid.coe_mul, ← mulVec_mulVec, hMfix j (by simp [hja, hjs])]
      exact planeRotationMatrix_mulVec_other hja hjb p q w

private lemma so_transpose_mul (R : Matrix.specialOrthogonalGroup ι ℝ) : R.valᵀ * R.val = 1 := by
  exact (Matrix.mem_orthogonalGroup_iff' ι ℝ).mp R.property.1

private lemma so_mulVec_norm (R : Matrix.specialOrthogonalGroup ι ℝ) (v : ι → ℝ) :
    (∑ j, (R.val.mulVec v j) ^ 2) = ∑ j, (v j) ^ 2 := by
  have h := dotProduct_transpose_mulVec R.val v (R.val.mulVec v)
  rw [mulVec_mulVec, so_transpose_mul, one_mulVec] at h
  simpa only [dotProduct, pow_two] using h.symm

private lemma so_column_norm (R : Matrix.specialOrthogonalGroup ι ℝ) (a : ι) :
    ∑ j, (R.val j a) ^ 2 = 1 := by
  have h := congrFun (congrFun (so_transpose_mul R) a) a
  simpa [mul_apply, transpose_apply, pow_two] using h

private lemma so_row_of_column (R : Matrix.specialOrthogonalGroup ι ℝ) (a : ι)
    (ha : ∀ j, R.val j a = if j = a then 1 else 0) :
    ∀ j, R.val a j = if a = j then 1 else 0 := by
  intro j
  have h := congrFun (congrFun (so_transpose_mul R) j) a
  simpa [mul_apply, transpose_apply, ha, one_apply, eq_comm] using h

private lemma so_column_of_row (R : Matrix.specialOrthogonalGroup ι ℝ) (a : ι)
    (ha : ∀ j, R.val a j = if a = j then 1 else 0) :
    ∀ j, R.val j a = if j = a then 1 else 0 := by
  have hR : R.val * R.valᵀ = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff ι ℝ).mp R.property.1
  intro j
  have h := congrFun (congrFun hR j) a
  simpa [mul_apply, transpose_apply, ha, one_apply, eq_comm] using h

private lemma reduce_unit_vector (G : Subgroup (Matrix.specialOrthogonalGroup ι ℝ))
    (hplane : ∀ a b p q hab hpq, coordinatePlaneRotation a b p q hab hpq ∈ G)
    (s : Finset ι) (a b : ι) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (v : ι → ℝ) (hvn : ∑ j, (v j) ^ 2 = 1) (hvs : ∀ j ∉ s, v j = 0) :
    ∃ M : Matrix.specialOrthogonalGroup ι ℝ, M ∈ G ∧
      (∀ j, M.val.mulVec v j = if j = a then 1 else 0) ∧
      (∀ j ∉ s, ∀ w : ι → ℝ, M.val.mulVec w j = w j) := by
  obtain ⟨p, q, hpq, hnonneg, -⟩ := choose_plane_parameters (v a) (v b)
  let A := coordinatePlaneRotation a b p q hab hpq
  have hAa : 0 ≤ A.val.mulVec v a := by
    simpa [A, coordinatePlaneRotation, planeRotationMatrix_mulVec_a hab] using hnonneg
  obtain ⟨M, hM, hMa, hMz, hMfix⟩ :=
    reduce_coordinates G hplane (s.erase a) a (by simp) (A.val.mulVec v) hAa
  let B := M * A
  have hBfix (j : ι) (hj : j ∉ s) (w : ι → ℝ) : B.val.mulVec w j = w j := by
    change (M.val * A.val).mulVec w j = w j
    rw [← mulVec_mulVec, hMfix j (by simpa [Finset.insert_erase ha] using hj)]
    exact planeRotationMatrix_mulVec_other (ne_of_mem_of_not_mem ha hj).symm
      (ne_of_mem_of_not_mem hb hj).symm p q w
  have hBzero (j : ι) (hja : j ≠ a) : B.val.mulVec v j = 0 := by
    by_cases hjs : j ∈ s
    · simpa only [B, Submonoid.coe_mul, ← mulVec_mulVec] using
        hMz j (Finset.mem_erase.mpr ⟨hja, hjs⟩)
    · rw [hBfix j hjs, hvs j hjs]
  have hBnonneg : 0 ≤ B.val.mulVec v a := by
    simpa only [B, Submonoid.coe_mul, ← mulVec_mulVec] using hMa
  have hBn : ∑ j, (B.val.mulVec v j) ^ 2 = 1 := (so_mulVec_norm B v).trans hvn
  have hBa : B.val.mulVec v a = 1 := by
    rw [Finset.sum_eq_single a] at hBn
    · nlinarith
    · intro j hj hja; rw [hBzero j hja]; norm_num
    · simp
  refine ⟨B, G.mul_mem hM (hplane a b p q hab hpq), ?_, hBfix⟩
  intro j
  by_cases hja : j = a
  · subst j; simpa using hBa
  · simpa [hja] using hBzero j hja

private lemma so_eq_one_of_fixed_except (R : Matrix.specialOrthogonalGroup ι ℝ) (a : ι)
    (hR : ∀ j, j ≠ a → ∀ i, R.val i j = if i = j then 1 else 0) : R = 1 := by
  have hrow (i : ι) (hi : i ≠ a) : ∀ j, R.val i j = if i = j then 1 else 0 :=
    so_row_of_column R i (hR i hi)
  have hdiag : R.val = diagonal (fun i => if i = a then R.val a a else 1) := by
    ext i j
    by_cases hia : i = a
    · subst i
      by_cases hja : j = a
      · subst j; simp
      · rw [hR j hja]
        simp [Ne.symm hja]
    · rw [hrow i hia]
      simp [diagonal_apply, hia]
  have hdet : R.val.det = 1 := R.property.2
  rw [hdiag, det_diagonal] at hdet
  simp at hdet
  apply Subtype.ext
  rw [hdiag]
  simp [hdet]

private lemma subgroup_contains_of_fixed (G : Subgroup (Matrix.specialOrthogonalGroup ι ℝ))
    (hplane : ∀ a b p q hab hpq, coordinatePlaneRotation a b p q hab hpq ∈ G)
    (s : Finset ι) :
    ∀ R : Matrix.specialOrthogonalGroup ι ℝ,
      (∀ j ∉ s, ∀ i, R.val i j = if i = j then 1 else 0) → R ∈ G := by
  refine Finset.strongInductionOn s ?_
  intro s ih R hR
  by_cases hs : s = ∅
  · have hRI : R = 1 := by
      apply Subtype.ext
      ext i j
      simpa [one_apply] using hR j (by simp [hs]) i
    rw [hRI]
    exact G.one_mem
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  by_cases hsa : s = {a}
  · have hRI : R = 1 := so_eq_one_of_fixed_except R a (by
      intro j hja
      exact hR j (by simp [hsa, hja]))
    rw [hRI]
    exact G.one_mem
  have hex : ∃ b ∈ s, b ≠ a := by
    by_contra! h
    apply hsa
    ext j
    simp only [Finset.mem_singleton]
    exact ⟨h j, fun hj => hj ▸ ha⟩
  obtain ⟨b, hb, hba⟩ := hex
  have hsupport (j : ι) (hj : j ∉ s) : R.val j a = 0 := by
    have hja : j ≠ a := fun h => hj (h ▸ ha)
    simpa [hja] using so_row_of_column R j (hR j hj) a
  obtain ⟨M, hM, hMv, hMfix⟩ := reduce_unit_vector G hplane s a b ha hb hba.symm
    (fun j => R.val j a) (so_column_norm R a) hsupport
  have hQfix (j : ι) (hj : j ∉ s.erase a) (i : ι) :
      (M * R).val i j = if i = j then 1 else 0 := by
    change M.val.mulVec (fun k => R.val k j) i = _
    by_cases hja : j = a
    · subst j
      exact hMv i
    · have hjs : j ∉ s := fun h => hj (Finset.mem_erase.mpr ⟨hja, h⟩)
      have hrow (k : ι) : M.val j k = if j = k then 1 else 0 := by
        have h := hMfix j hjs (Pi.single k 1)
        simpa [mulVec_single_one, Pi.single_apply, eq_comm] using h
      have hcol := so_column_of_row M j hrow i
      have he : (fun k => R.val k j) = Pi.single j 1 := by
        funext k
        simpa [Pi.single_apply, eq_comm] using hR j hjs k
      rw [he, mulVec_single_one]
      exact hcol
  have hQ : M * R ∈ G := ih (s.erase a) (Finset.erase_ssubset ha) (M * R) hQfix
  have h := G.mul_mem (G.inv_mem hM) hQ
  simpa only [inv_mul_cancel_left] using h

/-- A subgroup containing the coordinate-plane rotations contains every special
orthogonal matrix. The proof eliminates coordinates and uses determinant one
for the final one-dimensional restriction. -/
theorem specialOrthogonal_mem_of_planeRotations
    (G : Subgroup (Matrix.specialOrthogonalGroup ι ℝ))
    (hplane : ∀ a b p q hab hpq, coordinatePlaneRotation a b p q hab hpq ∈ G)
    (R : Matrix.specialOrthogonalGroup ι ℝ) : R ∈ G :=
  subgroup_contains_of_fixed G hplane Finset.univ R (by simp)

/-- Induction on coordinate-plane rotations for arbitrary finite real SO(n),
including the zero- and one-dimensional cases. -/
theorem specialOrthogonal_induction
    {P : Matrix.specialOrthogonalGroup ι ℝ → Prop}
    (h1 : P 1) (hmul : ∀ A B, P A → P B → P (A * B))
    (hinv : ∀ A, P A → P A⁻¹)
    (hplane : ∀ a b p q hab hpq, P (coordinatePlaneRotation a b p q hab hpq))
    (R : Matrix.specialOrthogonalGroup ι ℝ) : P R := by
  let G : Subgroup (Matrix.specialOrthogonalGroup ι ℝ) :=
    { carrier := P, one_mem' := h1, mul_mem' := fun hA hB => hmul _ _ hA hB,
      inv_mem' := fun hA => hinv _ hA }
  exact specialOrthogonal_mem_of_planeRotations G hplane R

end
end GaussianTesting
