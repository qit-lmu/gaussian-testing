module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CreationAnnihilation

@[expose] public section

/-!
# The ordered Majorana product for parity

The manuscript's product is ordered by mode, with the X Majorana before the
Y Majorana in each mode. Pairing successive factors preserves this order.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- The ordered product `c₁ c₂ ⋯ c₂ₘ`, grouped into consecutive mode pairs. -/
def orderedMajoranaProduct (m : ℕ) : Module.End ℂ (HF m) :=
  (List.ofFn fun k : Fin m => maj (k, false) * maj (k, true)).prod

private theorem majorana_pair_apply (k : Fin m) (f : HF m) (x : Qm m) :
    (maj (k, false) * maj (k, true)) f x =
      Complex.I * (if x k then (-1 : ℂ) else 1) * f x := by
  have h := congrArg (fun A : Module.End ℂ (HF m) => A f x)
    (majorana_pair_eq_two_fermionNumber_sub_id k)
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, fermionNumber_apply] at h
  change Complex.I * ((maj (k, false) * maj (k, true)) f x) = _ at h
  calc
    _ = -Complex.I * (Complex.I * ((maj (k, false) * maj (k, true)) f x)) := by
      simp [← mul_assoc]
    _ = -Complex.I * ((2 : ℂ) * (if x k then f x else 0) - f x) := by rw [h]
    _ = _ := by cases x k <;> simp; ring

private theorem majorana_pairs_apply (ks : List (Fin m)) (f : HF m) (x : Qm m) :
    (ks.map fun k => maj (k, false) * maj (k, true)).prod f x =
      Complex.I ^ ks.length * (ks.map fun k => if x k then (-1 : ℂ) else 1).prod * f x := by
  induction ks generalizing f with
  | nil => simp
  | cons k ks ih =>
    rw [List.map_cons, List.prod_cons]
    change ((maj (k, false) * maj (k, true))
      ((ks.map fun k => maj (k, false) * maj (k, true)).prod f)) x = _
    rw [majorana_pair_apply, ih]
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    ring

/-- The manuscript identity `Π = (-i)^m c₁ ⋯ c₂ₘ`, including the zero-mode case. -/
theorem parityOp_eq_majoranaProduct :
    (parityOp : Module.End ℂ (HF m)) = (-Complex.I) ^ m • orderedMajoranaProduct m := by
  ext f x
  have hp := majorana_pairs_apply (List.ofFn (id : Fin m → Fin m)) f x
  simp only [List.map_ofFn, Function.comp_id, List.length_ofFn, Fin.prod_ofFn] at hp
  change parityOp f x = (-Complex.I) ^ m * orderedMajoranaProduct m f x
  rw [orderedMajoranaProduct, hp, parityOp_apply]
  have hc : (-Complex.I) ^ m * Complex.I ^ m = 1 := by
    rw [← mul_pow]
    simp
  have hsign : (-1 : ℂ) ^ (Finset.univ.filter fun k => x k).card =
      ∏ k, (if x k then (-1 : ℂ) else 1) := by
    rw [← Finset.prod_filter]
    simp
  rw [hsign]
  linear_combination -(∏ k, (if x k then (-1 : ℂ) else 1)) * f x * hc

end
end GaussianTesting
