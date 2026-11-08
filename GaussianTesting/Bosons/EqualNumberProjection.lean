module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberPhase
public import GaussianTesting.Bosons.NumberRotation

@[expose] public section

/-!
# Equal total particle counts after the mean-zero circuit

The inverse circuit sends number vectors to the complex creation modes
that diagonalize the manuscript's Λ. Their eigenvalue is the negative
of the measured total-count difference, so their zero eigenspaces agree.
-/

namespace GaussianTesting

open Complex Finsupp
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

private theorem gmonC_fin2 {m : ℕ} (X : Fin 2 → Fin 2 → ℂ) (p q : Fin m → ℕ) :
    gmonC X ![p,q] = monWC
      (((List.finRange m).flatMap fun l => List.replicate (p l) (X 0,l)) ++
        ((List.finRange m).flatMap fun l => List.replicate (q l) (X 1,l))) := by
  have hL : (Finset.univ : Finset (Fin 2)).toList.Perm [0,1] := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (by decide)).mpr
    intro i
    fin_cases i <;> simp
  apply monWC_perm
  change ((Finset.univ : Finset (Fin 2)).toList.flatMap fun s =>
    (List.finRange m).flatMap fun l => List.replicate (![p,q] s l) (X s,l)).Perm _
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    hL.flatMap (f := fun s => (List.finRange m).flatMap fun l =>
      List.replicate (![p,q] s l) (X s,l)) (fun _ _ => List.Perm.refl _)

private theorem gmonC_swapped {m : ℕ} (X : Fin 2 → Fin 2 → ℂ) (p q : Fin m → ℕ) :
    gmonC ![X 1, X 0] ![p,q] = gmonC X ![q,p] := by
  rw [gmonC_fin2, gmonC_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact monWC_perm List.perm_append_comm

/-- The inverse circuit is the negative-angle splitter followed by the
inverse phase on register two. Its action is first defined on finite vectors. -/
def equalNumberInverseSub (m : ℕ) : FA2 m →ₗ[ℂ] FA2 m :=
  numberPhaseSub m Complex.I ∘ₗ Vsub m

/-- On each occupation vector the inverse circuit diagonalizes Λ, with
exactly the sign stated in the source note for Figure 1(b). -/
theorem equalNumberInverseSub_eigen {m : ℕ}
    (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    lambdaB m (equalNumberInverseSub m (Finsupp.single p 1)) =
      ((degB p.2 : ℂ) - (degB p.1 : ℂ)) •
        equalNumberInverseSub m (Finsupp.single p 1) := by
  have hmodes : (fun s => ![rotInvModes s 0, Complex.I * rotInvModes s 1]) =
      ![pmModes 1, pmModes 0] := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [rotInvModes, pmModes, cPlus, cMinus]
  simp only [equalNumberInverseSub, LinearMap.comp_apply, Vsub,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul, map_smul,
    numberPhaseSub_gmonC, hmodes, gmonC_swapped, lambdaB_gmonC,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [smul_comm]

/-- The measured total-number difference on finite number-basis vectors. -/
def totalNumberDifferenceSub (m : ℕ) : FA2 m →ₗ[ℂ] FA2 m :=
  Finsupp.lsum ℂ fun p => ((degB p.1 : ℂ) - (degB p.2 : ℂ)) • Finsupp.lsingle p

/-- The circuit intertwines total-number difference with `-Λ` on the
finite-particle core, with the sign in the manuscript's Figure 1(b) note. -/
theorem equalNumberInverseSub_numberDifference (m : ℕ) :
    equalNumberInverseSub m ∘ₗ totalNumberDifferenceSub m =
      -(lambdaB m ∘ₗ equalNumberInverseSub m) := by
  apply Finsupp.lhom_ext
  intro p c
  have hc : Finsupp.single p c = c • Finsupp.single p 1 := by simp
  rw [hc, map_smul, map_smul]
  congr 1
  change equalNumberInverseSub m (totalNumberDifferenceSub m (Finsupp.single p 1)) =
    -lambdaB m (equalNumberInverseSub m (Finsupp.single p 1))
  simp only [totalNumberDifferenceSub, Finsupp.lsum_single, LinearMap.smul_apply,
    Finsupp.lsingle_apply, map_smul, equalNumberInverseSub_eigen]
  rw [← neg_smul]
  congr 1
  ring

/-- The positive balanced splitter, as a unitary in occupation coordinates. -/
def balancedFockSplitter (m : ℕ) : FockB2 m ≃ₗᵢ[ℂ] FockB2 m :=
  { (ULp m).toLinearMap with
    invFun := VLp m
    left_inv := fun f => DFunLike.congr_fun (VLp_ULp m) f
    right_inv := fun f => DFunLike.congr_fun (ULp_VLp m) f
    norm_map' := fun f => norm_ULp f }

private theorem VLp_embedFA2 (m : ℕ) (f : FA2 m) :
    VLp m (embedFA2 f) = embedFA2 (Vsub m f) := by
  apply (balancedFockSplitter m).injective
  change ULp m (VLp m (embedFA2 f)) = ULp m (embedFA2 (Vsub m f))
  have hi : Usub m (Vsub m f) = f := LinearMap.congr_fun (Usub_Vsub m) f
  rw [ULp_embedFA2, hi]
  exact DFunLike.congr_fun (ULp_VLp m) (embedFA2 f)

/-- Inverse of the phase-shift/positive-splitter circuit in Figure 1(b). -/
def equalNumberCircuitInverse (m : ℕ) : FockB2 m ≃ₗᵢ[ℂ] FockB2 m :=
  (balancedFockSplitter m).symm.trans (numberPhase m Complex.I (by simp))

private theorem equalNumberCircuitInverse_embed (m : ℕ) (f : FA2 m) :
    equalNumberCircuitInverse m (embedFA2 f) = embedFA2 (equalNumberInverseSub m f) := by
  change numberPhase m Complex.I (by simp) (VLp m (embedFA2 f)) = _
  rw [VLp_embedFA2, numberPhase_embedFA2]
  rfl

/-- The accepting event of the two total-number measurements is equality
of the sums of the mode occupations in the two registers. -/
def equalTotalNumberProjection (m : ℕ) : FockB2 m →L[ℂ] FockB2 m := by
  classical
  refine LinearMap.mkContinuous
    { toFun := fun f => ⟨fun p => if degB p.1 = degB p.2 then f p else 0, ?_⟩
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · apply (lp.memℓp f).mono'
    intro p
    split_ifs <;> simp
  · intro f g
    ext p
    change (if degB p.1 = degB p.2 then f p + g p else 0) =
      (if degB p.1 = degB p.2 then f p else 0) + (if degB p.1 = degB p.2 then g p else 0)
    split_ifs <;> simp
  · intro c f
    ext p
    change (if _ then c * f p else 0) = c * (if _ then f p else 0)
    split_ifs <;> simp
  · intro f
    simp only [one_mul]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro p
    change ‖if degB p.1 = degB p.2 then f p else 0‖ ≤ ‖f p‖
    split_ifs <;> simp

@[simp] theorem equalTotalNumberProjection_apply (m : ℕ) (f : FockB2 m)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    equalTotalNumberProjection m f p = if degB p.1 = degB p.2 then f p else 0 := rfl

private theorem equalTotalNumberProjection_single (m : ℕ)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) (c : ℂ) :
    equalTotalNumberProjection m (lp.single 2 p c) =
      if degB p.1 = degB p.2 then lp.single 2 p c else 0 := by
  classical
  ext q
  by_cases hpq : p = q
  · subst q
    split_ifs <;> simp [*]
  · by_cases hd : degB p.1 = degB p.2 <;>
      simp [equalTotalNumberProjection_apply, lp.single_apply, hpq, hd]

private theorem P0B_embedFA2_eigen {m : ℕ} (f : FA2 m) (c : ℂ)
    (hf : lambdaB m f = c • f) :
    P0B m (embedFA2 f) = if c = 0 then embedFA2 f else 0 := by
  classical
  have he (n : ℕ) : lambdaBlock m n (blockProj degB2 (embedFA2 f) n) =
      c • blockProj degB2 (embedFA2 f) n := by
    rw [← blockProj_embedFA2_lambdaB, hf, embedFA2_smul]
    rfl
  have hp (n : ℕ) : (LinearMap.ker (lambdaBlock m n)).starProjection
      (blockProj degB2 (embedFA2 f) n) =
        if c = 0 then blockProj degB2 (embedFA2 f) n else 0 := by
    split_ifs with hc
    · apply (LinearMap.ker (lambdaBlock m n)).starProjection_eq_self_iff.mpr
      rw [LinearMap.mem_ker, he, hc, zero_smul]
    · apply (LinearMap.ker (lambdaBlock m n)).eq_starProjection_of_mem_of_inner_eq_zero
        (Submodule.zero_mem _)
      intro w hw
      have h := lambdaBlock_isSymmetric m n (blockProj degB2 (embedFA2 f) n) w
      rw [he, LinearMap.mem_ker.mp hw, inner_zero_right, inner_smul_left] at h
      simp only [sub_zero]
      exact (mul_eq_zero.mp h).resolve_left (by simpa using hc)
  ext p
  change (LinearMap.ker (lambdaBlock m (degB2 p))).starProjection
    (blockProj degB2 (embedFA2 f) (degB2 p)) ⟨p,rfl⟩ = _
  rw [hp]
  split_ifs <;> rfl

/-- The finite-particle diagonalization determines the entire accepting
projection, because number vectors span a dense subspace. -/
theorem P0B_equalNumberCircuitInverse (m : ℕ) :
    (P0B m).comp (equalNumberCircuitInverse m).toLinearIsometry.toContinuousLinearMap =
      (equalNumberCircuitInverse m).toLinearIsometry.toContinuousLinearMap.comp
        (equalTotalNumberProjection m) := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num)
  intro p
  apply ContinuousLinearMap.ext
  intro c
  change P0B m (equalNumberCircuitInverse m (lp.single 2 p c)) =
    equalNumberCircuitInverse m (equalTotalNumberProjection m (lp.single 2 p c))
  have hp : (lp.single 2 p 1 : FockB2 m) = embedFA2 (Finsupp.single p 1) := by
    ext q
    simp [lp.single_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have h := P0B_embedFA2_eigen (equalNumberInverseSub m (Finsupp.single p 1))
    ((degB p.2 : ℂ) - (degB p.1 : ℂ)) (equalNumberInverseSub_eigen p)
  have hc : (lp.single 2 p c : FockB2 m) = c • lp.single 2 p 1 := by
    ext q
    simp [lp.single_apply, Pi.single_apply]
  rw [hc, map_smul, map_smul, map_smul, map_smul]
  congr 1
  rw [equalTotalNumberProjection_single, hp, equalNumberCircuitInverse_embed]
  by_cases hd : degB p.1 = degB p.2
  · simp only [ite_eq_left hd, equalNumberCircuitInverse_embed]
    simpa only [hd, sub_self, ite_true] using h
  · simp only [ite_eq_right hd, map_zero]
    have hne : (degB p.2 : ℂ) - (degB p.1 : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast Ne.symm hd)
    simpa only [ite_eq_right hne] using h

/-- **Figure 1(b), in number coordinates.** The phase/beam-splitter circuit
followed by equal total counts has exactly the accepting projection `P₀`. -/
theorem equalNumberCircuit_conj_projection (m : ℕ) :
    (equalNumberCircuitInverse m).conjStarAlgEquiv (equalTotalNumberProjection m) = P0B m := by
  ext f : 1
  have h := DFunLike.congr_fun (P0B_equalNumberCircuitInverse m)
    ((equalNumberCircuitInverse m).symm f)
  change equalNumberCircuitInverse m (equalTotalNumberProjection m
    ((equalNumberCircuitInverse m).symm f)) = P0B m f
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply] using h.symm

end
end GaussianTesting
