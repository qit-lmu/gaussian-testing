module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.PureCharacteristic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

/-!
# The continuous-character step in Proposition 6.3

The manuscript proves that the vacuum-normalized characteristic function is
a continuous character, then identifies it with the exponential of a real
linear functional. This file records that part of the proposition's proof.
-/

namespace GaussianTesting

open scoped InnerProductSpace

noncomputable section

/-- Every continuous unit-circle character of a real normed space is the
exponential of a continuous real linear functional. -/
theorem continuous_character_eq_exp_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : E → ℂ} (hχ : Continuous χ) (hzero : χ 0 = 1)
    (hadd : ∀ x y, χ (x+y) = χ x * χ y) (hnorm : ∀ x, ‖χ x‖ = 1) :
    ∃ L : E →L[ℝ] ℝ, ∀ x, χ x = Complex.exp (Complex.I * (L x : ℂ)) := by
  let c : C(E, Circle) := ⟨fun x => ⟨χ x, by
    exact mem_sphere_zero_iff_norm.mpr (hnorm x)⟩,
    hχ.subtype_mk (fun x => mem_sphere_zero_iff_norm.mpr (hnorm x))⟩
  have hc0 : c 0 = 1 := Subtype.ext hzero
  have hca (x y : E) : c (x+y) = c x * c y := Subtype.ext (hadd x y)
  obtain ⟨f, ⟨hf0, hfe⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    c (0 : E) 0 (by simpa using hc0.symm)
  have he (x : E) : Circle.exp (f x) = c x := congrFun hfe x
  let d (p : E × E) : ℝ := f (p.1+p.2) - f p.1 - f p.2
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hde (p : E × E) : Circle.exp (d p) = 1 := by
    simp only [d, Circle.exp_sub, he, hca]
    rw [mul_div_cancel_left, div_self']
  have hfa (x y : E) : f (x+y) = f x + f y := by
    have h := Circle.isCoveringMap_exp.const_of_comp hd
      (fun p q => (hde p).trans (hde q).symm) (x,y) (0,0)
    dsimp [d] at h
    simp only [zero_add, hf0, sub_zero] at h
    linarith
  let a : E →+ ℝ := { toFun := f, map_zero' := hf0, map_add' := hfa }
  refine ⟨a.toRealLinearMap f.continuous, fun x => ?_⟩
  change χ x = Complex.exp (Complex.I * (f x : ℂ))
  have hx := congrArg (fun z : Circle => (z : ℂ)) (he x)
  change Complex.exp ((f x : ℂ) * Complex.I) = χ x at hx
  simpa only [mul_comm] using hx.symm

/-- Nondegeneracy of the manuscript's symplectic form realizes every real
linear phase as a displacement parameter. -/
theorem exists_waveSymplectic_eq_linear {m : ℕ} (L : WavePhase m →L[ℝ] ℝ) :
    ∃ a : WavePhase m, ∀ r, waveSymplectic a r = L r := by
  let Lq : WaveConfig m →L[ℝ] ℝ :=
    L.comp (ContinuousLinearMap.inl ℝ (WaveConfig m) (WaveConfig m))
  let Lp : WaveConfig m →L[ℝ] ℝ :=
    L.comp (ContinuousLinearMap.inr ℝ (WaveConfig m) (WaveConfig m))
  let u := (InnerProductSpace.toDual ℝ (WaveConfig m)).symm Lq
  let v := (InnerProductSpace.toDual ℝ (WaveConfig m)).symm Lp
  refine ⟨(v,-u), ?_⟩
  rintro ⟨q,p⟩
  change inner ℝ v p - inner ℝ (-u) q = L (q,p)
  rw [inner_neg_left, sub_neg_eq_add]
  change inner ℝ ((InnerProductSpace.toDual ℝ (WaveConfig m)).symm Lp) p +
    inner ℝ ((InnerProductSpace.toDual ℝ (WaveConfig m)).symm Lq) q = _
  rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]
  change L (0,p) + L (q,0) = L (q,p)
  rw [← map_add]
  congr 1
  simp

/-- The linear character in Proposition 6.3 is precisely a Weyl
displacement phase, in the manuscript's convention. -/
theorem continuous_character_eq_weyl_phase {m : ℕ} {χ : WavePhase m → ℂ}
    (hχ : Continuous χ) (hzero : χ 0 = 1)
    (hadd : ∀ r s, χ (r+s) = χ r * χ s) (hnorm : ∀ r, ‖χ r‖ = 1) :
    ∃ a : WavePhase m, ∀ r,
      χ r = Complex.exp (Complex.I * (waveSymplectic a r : ℂ)) := by
  obtain ⟨L, hL⟩ := continuous_character_eq_exp_linear hχ hzero hadd hnorm
  obtain ⟨a, ha⟩ := exists_waveSymplectic_eq_linear L
  exact ⟨a, fun r => by rw [ha, hL]⟩

end
end GaussianTesting
