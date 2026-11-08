module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Differentiating finite scalar expansions

Polynomial orbits admit finite expansions in fixed polynomial vectors. The scalar
coefficients can therefore be differentiated after any linear realization into a
normed space, without placing an artificial norm on the polynomial space.
-/

namespace GaussianTesting

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A curve has a finite scalar expansion whose coefficients have the indicated
derivatives. This is an algebraic certificate, not a topology on `V`. -/
def HasFiniteCurveDeriv (f : ℝ → V) (f' : V) (t : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℝ → ℂ) (c' : κ → ℂ) (v : κ → V),
    (∀ i, HasDerivAt (c i) (c' i) t) ∧
    (∀ s, f s = ∑ i, c i s • v i) ∧ f' = ∑ i, c' i • v i

namespace HasFiniteCurveDeriv

lemma const (v : V) (t : ℝ) : HasFiniteCurveDeriv (fun _ => v) 0 t := by
  refine ⟨Unit, inferInstance, (fun _ _ => 1), (fun _ => 0), (fun _ => v), ?_, ?_, ?_⟩
  · intro i
    exact hasDerivAt_const t (1 : ℂ)
  · intro s
    simp
  · simp

lemma scalar (c : ℝ → ℂ) (c' : ℂ) (v : V) (t : ℝ)
    (hc : HasDerivAt c c' t) : HasFiniteCurveDeriv (fun s => c s • v) (c' • v) t := by
  exact ⟨Unit, inferInstance, (fun _ => c), (fun _ => c'), (fun _ => v),
    (fun _ => hc), (by intro s; simp), (by simp)⟩

lemma add {f g : ℝ → V} {f' g' : V} {t : ℝ}
    (hf : HasFiniteCurveDeriv f f' t) (hg : HasFiniteCurveDeriv g g' t) :
    HasFiniteCurveDeriv (fun s => f s + g s) (f' + g') t := by
  classical
  obtain ⟨κ, hκ, c, c', v, hc, hfc, hf'⟩ := hf
  obtain ⟨η, hη, d, d', w, hd, hgd, hg'⟩ := hg
  let := hκ
  let := hη
  refine ⟨κ ⊕ η, inferInstance, Sum.elim c d, Sum.elim c' d', Sum.elim v w, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hd i
  · intro s
    simp [Fintype.sum_sum_type, hfc, hgd]
  · simp [Fintype.sum_sum_type, hf', hg']

/-- Every linear realization of a finite differentiable expansion has the
corresponding derivative in the target normed space. -/
lemma map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {f : ℝ → V} {f' : V} {t : ℝ} (hf : HasFiniteCurveDeriv f f' t)
    (L : V →ₗ[ℂ] E) : HasDerivAt (fun s => L (f s)) (L f') t := by
  classical
  obtain ⟨κ, hκ, c, c', v, hc, hfc, hf'⟩ := hf
  let := hκ
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hc i).smul_const (L (v i)))
  simpa only [hfc, hf', map_sum, map_smul, Finset.sum_fn] using h

end HasFiniteCurveDeriv

section Algebra

variable {A : Type*} [CommRing A] [Algebra ℂ A]

lemma HasFiniteCurveDeriv.mul {f g : ℝ → A} {f' g' : A} {t : ℝ}
    (hf : HasFiniteCurveDeriv f f' t) (hg : HasFiniteCurveDeriv g g' t) :
    HasFiniteCurveDeriv (fun s => f s * g s) (f' * g t + f t * g') t := by
  classical
  obtain ⟨κ, hκ, c, c', v, hc, hfc, hf'⟩ := hf
  obtain ⟨η, hη, d, d', w, hd, hgd, hg'⟩ := hg
  let := hκ
  let := hη
  refine ⟨κ × η, inferInstance, (fun i s => c i.1 s * d i.2 s),
    (fun i => c' i.1 * d i.2 t + c i.1 t * d' i.2),
    (fun i => v i.1 * w i.2), ?_, ?_, ?_⟩
  · intro i
    exact (hc i.1).mul (hd i.2)
  · intro s
    dsimp only
    rw [hfc, hgd, Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [smul_smul, mul_comm]
  · rw [hf', hg', hfc, hgd, Fintype.sum_prod_type]
    simp only [add_smul, Finset.sum_add_distrib, Finset.sum_mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;>
      simp [smul_smul, mul_comm]

end Algebra

end

end GaussianTesting
