module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.Lambda
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The product Bell basis in Figure 1(a)

The outcome consists of a phase bit and a parity bit for each mode.
The local Bell vector is `( |0,b⟩ + (-1)^a |1,!b⟩ ) / √2`.
Taking products over modes gives an orthonormal basis of the two registers;
its coefficient isometry is the Bell readout unitary `U_Bell`.
-/

namespace GaussianTesting

open scoped InnerProductSpace ComplexConjugate
open Finset

noncomputable section

/-- The normalization of a Bell pair. -/
def bellScale : ℂ := (Real.sqrt 2 : ℂ)⁻¹

@[simp] theorem star_bellScale : starRingEnd ℂ bellScale = bellScale := by
  simp [bellScale]

theorem bellScale_sq : bellScale ^ 2 = (1 / 2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp [bellScale, inv_pow, hs]

/-- Local Bell coefficients: `a` is the phase bit and `b` the parity bit. -/
def bellLocalAmplitude (a b x y : Bool) : ℂ :=
  if y = Bool.xor x b then (if a && x then -1 else 1) * bellScale else 0

@[simp] theorem star_bellLocalAmplitude (a b x y : Bool) :
    starRingEnd ℂ (bellLocalAmplitude a b x y) = bellLocalAmplitude a b x y := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp [bellLocalAmplitude]

theorem bellLocalAmplitude_inner (a b c d : Bool) :
    (∑ x : Bool, ∑ y : Bool,
      starRingEnd ℂ (bellLocalAmplitude a b x y) * bellLocalAmplitude c d x y) =
      if (a, b) = (c, d) then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [bellLocalAmplitude] <;>
    ring_nf <;> norm_num [bellScale_sq]

/-- Bell vectors across the two `m`-mode registers, as products of Bell pairs. -/
def fermionicBellVector (m : ℕ) (z : Qm m × Qm m) : H2 (Qm m) :=
  WithLp.toLp 2 fun p => ∏ k, bellLocalAmplitude (z.1 k) (z.2 k) (p.1 k) (p.2 k)

@[simp] theorem fermionicBellVector_apply (m : ℕ) (z p : Qm m × Qm m) :
    fermionicBellVector m z p =
      ∏ k, bellLocalAmplitude (z.1 k) (z.2 k) (p.1 k) (p.2 k) := rfl

private def bitPairEquiv (m : ℕ) : (Qm m × Qm m) ≃ (Fin m → Bool × Bool) where
  toFun p k := (p.1 k, p.2 k)
  invFun f := (fun k => (f k).1, fun k => (f k).2)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem sum_pair_prod (m : ℕ) (f : Fin m → Bool → Bool → ℂ) :
    (∑ p : Qm m × Qm m, ∏ k, f k (p.1 k) (p.2 k)) =
      ∏ k, ∑ x : Bool, ∑ y : Bool, f k x y := by
  calc
    _ = ∑ q : Fin m → Bool × Bool, ∏ k, f k (q k).1 (q k).2 :=
      Fintype.sum_equiv (bitPairEquiv m) _ _ (fun _ => rfl)
    _ = ∏ k, ∑ p : Bool × Bool, f k p.1 p.2 :=
      (Fintype.prod_sum (fun (k : Fin m) (p : Bool × Bool) => f k p.1 p.2)).symm
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- Orthogonality of the product Bell vectors, for every mode count. -/
theorem fermionicBellVector_inner (m : ℕ) (z w : Qm m × Qm m) :
    inner ℂ (fermionicBellVector m z) (fermionicBellVector m w) =
      if z = w then 1 else 0 := by
  classical
  simp only [PiLp.inner_apply, RCLike.inner_apply, fermionicBellVector_apply,
    map_prod, ← Finset.prod_mul_distrib]
  rw [sum_pair_prod m (fun k x y =>
    bellLocalAmplitude (w.1 k) (w.2 k) x y *
      starRingEnd ℂ (bellLocalAmplitude (z.1 k) (z.2 k) x y))]
  have hlocal (k : Fin m) :
      (∑ x : Bool, ∑ y : Bool,
        bellLocalAmplitude (w.1 k) (w.2 k) x y *
          starRingEnd ℂ (bellLocalAmplitude (z.1 k) (z.2 k) x y)) =
        if (z.1 k, z.2 k) = (w.1 k, w.2 k) then 1 else 0 := by
    simpa only [mul_comm] using bellLocalAmplitude_inner (z.1 k) (z.2 k) (w.1 k) (w.2 k)
  simp only [hlocal]
  by_cases h : z = w
  · subst w; simp
  · rw [ite_eq_right h]
    have hex : ∃ k, (z.1 k, z.2 k) ≠ (w.1 k, w.2 k) := by
      by_contra! he
      apply h
      apply Prod.ext <;> funext k
      · exact congrArg Prod.fst (he k)
      · exact congrArg Prod.snd (he k)
    obtain ⟨k, hk⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)

theorem fermionicBellVector_orthonormal (m : ℕ) :
    Orthonormal ℂ (fermionicBellVector m) := by
  classical
  exact orthonormal_iff_ite.mpr (fermionicBellVector_inner m)

/-- The product Bell basis, labelled by phase and parity outcome bitstrings. -/
def fermionicBellBasis (m : ℕ) :
    OrthonormalBasis (Qm m × Qm m) ℂ (H2 (Qm m)) :=
  (basisOfOrthonormalOfCardEqFinrank (fermionicBellVector_orthonormal m)
    (by simp)).toOrthonormalBasis (by simpa using fermionicBellVector_orthonormal m)

@[simp] theorem fermionicBellBasis_apply (m : ℕ) (z : Qm m × Qm m) :
    fermionicBellBasis m z = fermionicBellVector m z := by
  simp [fermionicBellBasis]

/-- Figure 1(a)'s unitary sends Bell vectors to their classical bitstring labels. -/
def fermionicBellReadout (m : ℕ) : H2 (Qm m) ≃ₗᵢ[ℂ] H2 (Qm m) :=
  (fermionicBellBasis m).repr

@[simp] theorem fermionicBellReadout_basis (m : ℕ) (z : Qm m × Qm m) :
    fermionicBellReadout m (fermionicBellBasis m z) = EuclideanSpace.single z 1 := by
  exact (fermionicBellBasis m).repr_self z

@[simp] theorem fermionicBellReadout_symm_single (m : ℕ) (z : Qm m × Qm m) :
    (fermionicBellReadout m).symm (EuclideanSpace.single z 1) =
      fermionicBellBasis m z :=
  (fermionicBellBasis m).repr_symm_single z

/-- The explicit Bell readout matrix, with one real Bell amplitude per mode. -/
theorem fermionicBellReadout_apply (m : ℕ) (f : H2 (Qm m)) (z : Qm m × Qm m) :
    fermionicBellReadout m f z =
      ∑ p : Qm m × Qm m, f p *
        ∏ k, bellLocalAmplitude (z.1 k) (z.2 k) (p.1 k) (p.2 k) := by
  change (fermionicBellBasis m).repr f z = _
  rw [OrthonormalBasis.repr_apply_apply, fermionicBellBasis_apply]
  simp only [PiLp.inner_apply, RCLike.inner_apply, fermionicBellVector_apply,
    map_prod, star_bellLocalAmplitude]

end
end GaussianTesting
