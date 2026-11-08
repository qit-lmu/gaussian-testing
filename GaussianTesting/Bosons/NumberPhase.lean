module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.BeamSplitter
public import GaussianTesting.Bosons.ClosedLambda

@[expose] public section

/-!
# The number-basis phase used in Figure 1(b)

A phase `z` on every mode of the second register multiplies its occupation
vector `q` by `z ^ |q|`. The circuit uses `z = -i`, the phase shift by π/2
with the manuscript's convention. This file constructs that unitary and
its finite-particle action, without an unbounded exponential assumption.
-/

namespace GaussianTesting

open Complex Finsupp
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 2048

/-- Phase every mode of register two in the finite-particle space. -/
def numberPhaseSub (m : ℕ) (z : ℂ) : FA2 m →ₗ[ℂ] FA2 m :=
  Finsupp.lsum ℂ fun p => (z ^ degB p.2) • Finsupp.lsingle p

@[simp] theorem numberPhaseSub_single {m : ℕ} (z : ℂ)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) (c : ℂ) :
    numberPhaseSub m z (Finsupp.single p c) =
      (z ^ degB p.2) • Finsupp.single p c := by
  simp [numberPhaseSub, Finsupp.lsum_single]

@[simp] theorem numberPhaseSub_apply {m : ℕ} (z : ℂ) (f : FA2 m)
    (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    numberPhaseSub m z f p = z ^ degB p.2 * f p := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, mul_add]
  | single q c =>
    simp only [numberPhaseSub_single, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h
    · subst q; rfl
    · simp

@[simp] theorem numberPhaseSub_vac {m : ℕ} (z : ℂ) :
    numberPhaseSub m z (vac2 (m := m)) = vac2 := by simp [vac2, degB]

private theorem degB_increase {m : ℕ} (q : Fin m → ℕ) (l : Fin m) :
    degB (Function.update q l (q l + 1)) = degB q + 1 := by
  classical
  unfold degB
  have h := Finset.sum_update_of_mem (Finset.mem_univ l) q (q l + 1)
  simp only [Finset.sdiff_singleton_eq_erase] at h
  have he := Finset.sum_erase_add Finset.univ q (Finset.mem_univ l)
  omega

/-- The phase rotates the second coefficient of a creation mode. -/
theorem numberPhaseSub_admC {m : ℕ} (z : ℂ) (c : Fin 2 → ℂ) (l : Fin m) :
    numberPhaseSub m z ∘ₗ AdmC c l = AdmC ![c 0, z * c 1] l ∘ₗ numberPhaseSub m z := by
  classical
  apply Finsupp.lhom_ext
  intro p a
  have ha : Finsupp.single p a = a • Finsupp.single p 1 := by simp
  rw [ha, map_smul, map_smul]
  congr 1
  simp [AdmC, copyL, copyR, adF, Finsupp.lsum_single,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  ext q
  simp only [Finsupp.add_apply,
    Finsupp.single_apply]
  split_ifs with hL hR
  · subst q
    have h := congrArg (fun x : (Fin m → ℕ) × (Fin m → ℕ) => x.1 l) hR
    simp at h
  · subst q
    ring
  · subst q
    simp only [degB_increase, pow_succ]
    ring
  · simp

/-- Phase action on a creation monomial. -/
theorem numberPhaseSub_gmonC {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : ℂ) (X : κ → Fin 2 → ℂ) (α : κ → Fin m → ℕ) :
    numberPhaseSub m z (gmonC X α) = gmonC (fun s => ![X s 0, z * X s 1]) α := by
  have hw (L : List ((Fin 2 → ℂ) × Fin m)) :
      numberPhaseSub m z (monWC L) =
        monWC (L.map fun x => (![x.1 0, z * x.1 1], x.2)) := by
    induction L with
    | nil => simp [monWC, numberPhaseSub_vac]
    | cons x L ih =>
      simp only [monWC_cons, List.map_cons]
      have h := LinearMap.congr_fun (numberPhaseSub_admC z x.1 x.2) (monWC L)
      simpa only [LinearMap.comp_apply, ih] using h
  rw [gmonC, hw]
  congr 1
  simp only [expWordC, List.map_flatMap, List.map_replicate]

private theorem numberPhase_mem {m : ℕ} (z : ℂ) (hz : ‖z‖ = 1) (f : FockB2 m) :
    Memℓp (fun p : (Fin m → ℕ) × (Fin m → ℕ) => z ^ degB p.2 * f p) 2 := by
  apply (lp.memℓp f).mono'
  intro p
  simp [norm_pow, hz]

def numberPhaseLinear (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    FockB2 m →ₗ[ℂ] FockB2 m where
  toFun f := ⟨fun p => z ^ degB p.2 * f p, by exact numberPhase_mem z hz f⟩
  map_add' f g := by ext p; exact mul_add _ _ _
  map_smul' c f := by ext p; change _ * (c * _) = c * (_ * _); ring

private theorem numberPhaseLinear_norm (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) (f : FockB2 m) :
    ‖numberPhaseLinear m z hz f‖ = ‖f‖ := by
  apply le_antisymm <;> apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) <;>
    intro p <;> simp [numberPhaseLinear, norm_pow, hz]

/-- The unitary modewise phase on register two, acting in the number basis. -/
def numberPhase (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) : FockB2 m ≃ₗᵢ[ℂ] FockB2 m :=
  { numberPhaseLinear m z hz with
    invFun := numberPhaseLinear m (star z) (by simpa using hz)
    left_inv := by
      intro f
      ext p
      change star z ^ degB p.2 * (z ^ degB p.2 * f p) = f p
      rw [← mul_assoc, ← mul_pow]
      have h : star z * z = 1 := by rw [Complex.star_def, Complex.conj_mul']; simp [hz]
      rw [h, one_pow, one_mul]
    right_inv := by
      intro f
      ext p
      change z ^ degB p.2 * (star z ^ degB p.2 * f p) = f p
      rw [← mul_assoc, ← mul_pow]
      have h : z * star z = 1 := by rw [mul_comm, Complex.star_def, Complex.conj_mul']; simp [hz]
      rw [h, one_pow, one_mul]
    norm_map' := by exact numberPhaseLinear_norm m z hz }

@[simp] theorem numberPhase_apply (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (f : FockB2 m) (p : (Fin m → ℕ) × (Fin m → ℕ)) :
    numberPhase m z hz f p = z ^ degB p.2 * f p := rfl

/-- The inverse phase shift by π/2 is the modewise phase `i`. -/
theorem numberPhase_negI_symm (m : ℕ) :
    (numberPhase m (-Complex.I) (by simp)).symm = numberPhase m Complex.I (by simp) := by
  ext f p
  change star (-Complex.I) ^ degB p.2 * f p = Complex.I ^ degB p.2 * f p
  simp

/-- The inverse of the modewise phase `i` is the circuit's phase `-i`. -/
theorem numberPhase_I_symm (m : ℕ) :
    (numberPhase m Complex.I (by simp)).symm = numberPhase m (-Complex.I) (by simp) := by
  ext f p
  change star Complex.I ^ degB p.2 * f p = (-Complex.I) ^ degB p.2 * f p
  simp

/-- The unitary phase agrees with its finite-particle formula. -/
theorem numberPhase_embedFA2 (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) (f : FA2 m) :
    numberPhase m z hz (embedFA2 f) = embedFA2 (numberPhaseSub m z f) := by
  ext p
  exact (numberPhaseSub_apply z f p).symm

end
end GaussianTesting
