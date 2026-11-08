module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.NumberProjection
public import GaussianTesting.Bosons.BeamSplitter

@[expose] public section

/-! # The balanced splitter in physical number coordinates -/

namespace GaussianTesting

open MvPolynomial

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem pderiv_polynomialRotate_zero (m : ℕ) (θ : ℝ) (j : Fin m)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    pderiv (0,j) (polynomialRotate m θ p) =
      (Real.cos θ : ℂ) • polynomialRotate m θ (pderiv (0,j) p) -
        (Real.sin θ : ℂ) • polynomialRotate m θ (pderiv (1,j) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]; module
  | mul_X p i hp =>
    rcases i with ⟨i,k⟩
    fin_cases i <;>
      by_cases h : k = j <;>
      simp [map_mul, polynomialRotate_X, hp, h,
        pderiv_X, Prod.ext_iff, Algebra.smul_def] <;> ring

private theorem pderiv_polynomialRotate_one (m : ℕ) (θ : ℝ) (j : Fin m)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    pderiv (1,j) (polynomialRotate m θ p) =
      (Real.sin θ : ℂ) • polynomialRotate m θ (pderiv (0,j) p) +
        (Real.cos θ : ℂ) • polynomialRotate m θ (pderiv (1,j) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]; module
  | mul_X p i hp =>
    rcases i with ⟨i,k⟩
    fin_cases i <;>
      by_cases h : k = j <;>
      simp [map_mul, polynomialRotate_X, hp, h,
        pderiv_X, Prod.ext_iff, Algebra.smul_def] <;> ring

/-- Coordinate rotation transforms first-copy creation as the manuscript's mode rotation. -/
theorem polynomialRotate_creation_zero (m : ℕ) (θ : ℝ) (j : Fin m)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialRotate m θ (polynomialCreation (0,j) p) =
      (Real.cos θ : ℂ) • polynomialCreation (0,j) (polynomialRotate m θ p) +
        (Real.sin θ : ℂ) • polynomialCreation (1,j) (polynomialRotate m θ p) := by
  have hcs : (Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hd : (Real.cos θ : ℂ) • pderiv (0,j) (polynomialRotate m θ p) +
      (Real.sin θ : ℂ) • pderiv (1,j) (polynomialRotate m θ p) =
        polynomialRotate m θ (pderiv (0,j) p) := by
    rw [pderiv_polynomialRotate_zero, pderiv_polynomialRotate_one]
    calc
      _ = ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) •
          polynomialRotate m θ (pderiv (0,j) p) := by module
      _ = _ := by rw [hcs, one_smul]
  simp only [polynomialCreation_apply, map_smul, map_sub, map_mul,
    polynomialRotate_X, ite_true]
  rw [← hd]
  simp only [add_mul, smul_mul_assoc]
  module

/-- Coordinate rotation transforms second-copy creation with the prescribed minus sign. -/
theorem polynomialRotate_creation_one (m : ℕ) (θ : ℝ) (j : Fin m)
    (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialRotate m θ (polynomialCreation (1,j) p) =
      -(Real.sin θ : ℂ) • polynomialCreation (0,j) (polynomialRotate m θ p) +
        (Real.cos θ : ℂ) • polynomialCreation (1,j) (polynomialRotate m θ p) := by
  have hcs : (Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have hd : -(Real.sin θ : ℂ) • pderiv (0,j) (polynomialRotate m θ p) +
      (Real.cos θ : ℂ) • pderiv (1,j) (polynomialRotate m θ p) =
        polynomialRotate m θ (pderiv (1,j) p) := by
    rw [pderiv_polynomialRotate_zero, pderiv_polynomialRotate_one]
    calc
      _ = ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) •
          polynomialRotate m θ (pderiv (1,j) p) := by module
      _ = _ := by rw [hcs, one_smul]
  simp only [polynomialCreation_apply, map_smul, map_sub, map_mul,
    polynomialRotate_X, show ¬(1 : Fin 2) = 0 by decide, ite_false]
  rw [← hd]
  simp only [add_mul, smul_mul_assoc, neg_mul]
  module

private def polynomialModeCreation (m : ℕ) (c : Fin 2 → ℂ) (j : Fin m) :
    MvPolynomial (Fin 2 × Fin m) ℂ →ₗ[ℂ] MvPolynomial (Fin 2 × Fin m) ℂ :=
  c 0 • polynomialCreation (0,j) + c 1 • polynomialCreation (1,j)

private theorem pairNumberPolynomialLinear_AdmC (m : ℕ) (c : Fin 2 → ℂ)
    (j : Fin m) (f : FA2 m) :
    pairNumberPolynomialLinear m (AdmC c j f) =
      polynomialModeCreation m c j (pairNumberPolynomialLinear m f) := by
  simp only [AdmC, polynomialModeCreation, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, pairNumberPolynomialLinear_copyL_adF,
    pairNumberPolynomialLinear_copyR_adF]

private theorem polynomialRotate_balanced_modeCreation (m : ℕ) (c : Fin 2 → ℂ)
    (j : Fin m) (p : MvPolynomial (Fin 2 × Fin m) ℂ) :
    polynomialRotate m (Real.pi / 4) (polynomialModeCreation m c j p) =
      polynomialModeCreation m (rotU c) j (polynomialRotate m (Real.pi / 4) p) := by
  have hs : (Real.sqrt 2 : ℂ) / 2 = (Real.sqrt 2 : ℂ)⁻¹ := by
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)
    have hsq : (Real.sqrt 2 : ℂ)^2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    field_simp
    exact hsq
  simp only [polynomialModeCreation, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, map_smul, polynomialRotate_creation_zero, polynomialRotate_creation_one,
    Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.ofReal_div, Complex.ofReal_ofNat,
    hs, rotU, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [div_eq_mul_inv]
  module

private theorem polynomialRotate_pair_vacuum (m : ℕ) (θ : ℝ) :
    polynomialRotate m θ (pairNumberPolynomialLinear m vac2) =
      pairNumberPolynomialLinear m vac2 := by
  have hz : pairOccupationEquiv m ((fun _ => 0),(fun _ => 0)) = (fun _ => 0) := by
    funext i
    rcases i with ⟨i,j⟩
    fin_cases i <;> simp
  simp only [vac2, pairNumberPolynomialLinear_single, one_smul, hz,
    schrodingerNumberPolynomial, fockNumberPolynomialRaw_zero, map_smul, map_one]

/-- The algebraic balanced splitter is the manuscript's actual coordinate rotation
on the finite creation-polynomial core. -/
theorem pairNumberPolynomialLinear_Usub (m : ℕ) (f : FA2 m) :
    pairNumberPolynomialLinear m (Usub m f) =
      polynomialRotate m (Real.pi / 4) (pairNumberPolynomialLinear m f) := by
  have hw (L : List ((Fin 2 → ℂ) × Fin m)) :
      pairNumberPolynomialLinear m (Usub m (monWC L)) =
        polynomialRotate m (Real.pi / 4) (pairNumberPolynomialLinear m (monWC L)) := by
    induction L with
    | nil =>
      simpa [monWC] using (polynomialRotate_pair_vacuum m (Real.pi/4)).symm
    | cons x L ih =>
      have h := LinearMap.congr_fun (Usub_admC x.1 x.2) (monWC L)
      simp only [LinearMap.comp_apply] at h
      rw [monWC_cons, h, pairNumberPolynomialLinear_AdmC, ih,
        pairNumberPolynomialLinear_AdmC, polynomialRotate_balanced_modeCreation]
  have he : (pairNumberPolynomialLinear m).comp (Usub m) =
      (polynomialRotate m (Real.pi / 4)).toLinearMap.comp (pairNumberPolynomialLinear m) := by
    apply Finsupp.lhom_ext
    rintro ⟨p,q⟩ z
    have h := hw (expWordC stdModes ![p,q])
    change pairNumberPolynomialLinear m (Usub m (gmonC stdModes ![p,q])) =
      polynomialRotate m (Real.pi / 4) (pairNumberPolynomialLinear m (gmonC stdModes ![p,q])) at h
    rw [gmonC_stdModes] at h
    simp only [map_smul] at h
    have hs := smul_right_injective _ (mul_ne_zero (nFact_ne_zero p) (nFact_ne_zero q)) h
    change pairNumberPolynomialLinear m (Usub m (Finsupp.single (p,q) z)) =
      polynomialRotate m (Real.pi / 4) (pairNumberPolynomialLinear m (Finsupp.single (p,q) z))
    rw [← Finsupp.smul_single_one (p,q) z]
    simpa only [map_smul, LinearMap.comp_apply] using congrArg (z • ·) hs
  exact LinearMap.congr_fun he f

private theorem blockProj_embedFA2_conserves (m : ℕ) (T : FA2 m →ₗ[ℂ] FA2 m)
    (hT : ConservesDeg2 T) (f : FA2 m) (n : ℕ) :
    blockProj degB2 (embedFA2 (T f)) n =
      toBlock2 T n (blockProj degB2 (embedFA2 f) n) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero =>
    have h : embedFA2 (0 : FA2 m) = 0 := by ext p; simp
    simp only [map_zero, h]
    change (0 : BlockSp (degB2 (m := m)) n) = toBlock2 T n 0
    rw [map_zero]
  | add f g hf hg =>
    have ha (f g : FockB2 m) : blockProj degB2 (f+g) n =
        blockProj degB2 f n + blockProj degB2 g n := rfl
    simp only [map_add, embedFA2_add, ha, hf, hg]
  | single p c =>
    by_cases hp : degB2 p = n
    · have hs : IsHomog2 n (Finsupp.single p c) := by
        intro q hq
        obtain ⟨rfl,_⟩ := (Finsupp.mem_support_single _ _ _).mp hq
        exact hp
      exact (toBlock2_homogToBlock2 hT hs).symm
    · have hin : blockProj degB2 (embedFA2 (Finsupp.single p c)) n = 0 := by
        ext q
        change Finsupp.single p c q.1 = 0
        exact Finsupp.single_eq_of_ne (fun he => hp (he ▸ q.2))
      rw [hin, map_zero]
      ext q
      change T (Finsupp.single p c) q.1 = 0
      rw [← Finsupp.smul_single_one p c, map_smul, Finsupp.smul_apply]
      have hz : T (Finsupp.single p 1) q.1 = 0 := by
        by_contra h
        exact hp ((hT p q.1 (Finsupp.mem_support_iff.mpr h)).symm.trans q.2)
      rw [hz, smul_zero]

/-- The bounded balanced splitter extends its algebraic finite-core substitution. -/
theorem ULp_embedFA2 (m : ℕ) (f : FA2 m) :
    ULp m (embedFA2 f) = embedFA2 (Usub m f) := by
  apply lp.ext
  funext p
  change toBlock2 (Usub m) (degB2 p) (blockProj degB2 (embedFA2 f) (degB2 p)) ⟨p,rfl⟩ = _
  exact congrArg (fun v : BlockSp (degB2 (m := m)) (degB2 p) => v ⟨p,rfl⟩)
    (blockProj_embedFA2_conserves m (Usub m) (conservesDeg2_Usub m) f (degB2 p)).symm

/-- Physical coordinate rotation and the number-model balanced splitter agree on all vectors. -/
theorem fockPairSchrodingerEquiv_ULp (m : ℕ) (f : FockB2 m) :
    fockPairSchrodingerEquiv m (ULp m f) =
      schrodingerRotation m (Real.pi / 4) (fockPairSchrodingerEquiv m f) := by
  let U := (fockPairSchrodingerEquiv m).toContinuousLinearEquiv.toContinuousLinearMap
  let R := (schrodingerRotation m (Real.pi/4)).toContinuousLinearEquiv.toContinuousLinearMap
  have he : U.comp (ULp m) = R.comp U := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro p
    apply ContinuousLinearMap.ext
    intro c
    have hs : (lp.single 2 p c : FockB2 m) = embedFA2 (Finsupp.single p c) := by
      apply lp.ext
      funext q
      simp [lp.single_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
    change fockPairSchrodingerEquiv m (ULp m (lp.single 2 p c)) =
      schrodingerRotation m (Real.pi/4) (fockPairSchrodingerEquiv m (lp.single 2 p c))
    rw [hs, ULp_embedFA2, fockPairSchrodingerEquiv_embedFA2,
      fockPairSchrodingerEquiv_embedFA2, pairNumberPolynomialLinear_Usub,
      polynomialGaussian_rotate]
  exact DFunLike.congr_fun he f

/-- The inverse splitter has exactly the manuscript's negative rotation angle. -/
theorem fockPairSchrodingerEquiv_VLp (m : ℕ) (f : FockB2 m) :
    fockPairSchrodingerEquiv m (VLp m f) =
      schrodingerRotation m (-(Real.pi / 4)) (fockPairSchrodingerEquiv m f) := by
  have h := fockPairSchrodingerEquiv_ULp m (VLp m f)
  have hi := DFunLike.congr_fun (ULp_VLp m) f
  change ULp m (VLp m f) = f at hi
  rw [hi] at h
  have he := congrArg (schrodingerRotation m (-(Real.pi/4))) h
  rw [← schrodingerRotation_add, neg_add_cancel, schrodingerRotation_zero] at he
  exact he.symm

end
end GaussianTesting
