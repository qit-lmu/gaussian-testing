module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerFockPair

@[expose] public section

/-! # Number vectors and the physical two-copy tensor product -/

namespace GaussianTesting

open MvPolynomial MeasureTheory
open scoped InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem polynomialCreation_rename {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (j : σ) (p : MvPolynomial σ ℂ) :
    polynomialCreation (f j) (rename f p) = rename f (polynomialCreation j p) := by
  simp only [polynomialCreation_apply, pderiv_rename hf, map_smul, map_sub,
    map_mul, rename_X]

private theorem creationWord_map {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) (l : List σ) :
    creationWord (l.map f) = rename f (creationWord l) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, creationWord_cons, ih, polynomialCreation_rename f hf]

/-- Product of polynomial factors on the separate physical copies. -/
def pairPolynomial (m : ℕ) (p q : MvPolynomial (Fin m) ℂ) :
    MvPolynomial (Fin 2 × Fin m) ℂ :=
  rename (Prod.mk (0 : Fin 2)) p * rename (Prod.mk (1 : Fin 2)) q

private theorem pderiv_other_copy (m : ℕ) (j : Fin m)
    (q : MvPolynomial (Fin m) ℂ) :
    pderiv (0,j) (rename (Prod.mk (1 : Fin 2)) q) = 0 := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X q k hq =>
    simp only [map_mul, rename_X, pderiv_mul, hq, zero_mul,
      pderiv_X_of_ne (by simp : ((1 : Fin 2),k) ≠ (0,j)), mul_zero, add_zero]

private theorem pairPolynomial_creation_left (m : ℕ) (j : Fin m)
    (p q : MvPolynomial (Fin m) ℂ) :
    polynomialCreation (0,j) (pairPolynomial m p q) =
      pairPolynomial m (polynomialCreation j p) q := by
  have hinj : Function.Injective (Prod.mk (0 : Fin 2) : Fin m → Fin 2 × Fin m) :=
    fun _ _ h => (Prod.mk.inj h).2
  simp only [pairPolynomial, polynomialCreation_apply, pderiv_mul,
    pderiv_rename hinj, pderiv_other_copy, mul_zero, add_zero,
    map_smul, map_sub, map_mul, rename_X]
  simp only [Algebra.smul_def]
  ring

private theorem creationWord_pair (m : ℕ) (l r : List (Fin m)) :
    creationWord (l.map (Prod.mk (0 : Fin 2)) ++ r.map (Prod.mk (1 : Fin 2))) =
      pairPolynomial m (creationWord l) (creationWord r) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.nil_append, creationWord_nil, pairPolynomial, map_one,
      one_mul]
    exact creationWord_map _ (fun _ _ h => (Prod.mk.inj h).2) r
  | cons j l ih =>
    simp only [List.map_cons, List.cons_append, creationWord_cons, ih,
      pairPolynomial_creation_left]

/-- Unnormalized ordered creation powers factor across the two physical copies. -/
theorem fockNumberPolynomialRaw_pair (m : ℕ) (p q : Fin m → ℕ) :
    fockNumberPolynomialRaw (pairOccupationEquiv m (p,q)) =
      pairPolynomial m (fockNumberPolynomialRaw p) (fockNumberPolynomialRaw q) := by
  obtain ⟨l,hl,he⟩ := exists_creationWord_eq_raw p
  obtain ⟨r,hr,hf⟩ := exists_creationWord_eq_raw q
  rw [← he, ← hf, ← creationWord_pair, creationWord_eq_fockNumberPolynomialRaw]
  congr 1
  funext i
  rcases i with ⟨i,j⟩
  have h0 : Function.Injective (Prod.mk (0 : Fin 2) : Fin m → Fin 2 × Fin m) :=
    fun _ _ h => (Prod.mk.inj h).2
  have h1 : Function.Injective (Prod.mk (1 : Fin 2) : Fin m → Fin 2 × Fin m) :=
    fun _ _ h => (Prod.mk.inj h).2
  fin_cases i
  · change p j = List.count ((0 : Fin 2),j)
      (l.map (Prod.mk (0 : Fin 2)) ++ r.map (Prod.mk (1 : Fin 2)))
    simp only [List.count_append,
      List.count_map_of_injective _ _ h0, hl]
    have h : List.count (0,j) (r.map (Prod.mk (1 : Fin 2))) = 0 := by
      apply List.count_eq_zero.mpr
      simp
    rw [h, add_zero]
  · change q j = List.count ((1 : Fin 2),j)
      (l.map (Prod.mk (0 : Fin 2)) ++ r.map (Prod.mk (1 : Fin 2)))
    simp only [List.count_append,
      List.count_map_of_injective _ _ h1, hr]
    have h : List.count (1,j) (l.map (Prod.mk (0 : Fin 2))) = 0 := by
      apply List.count_eq_zero.mpr
      simp
    rw [h, zero_add]

private theorem numberNormalization_pair (m : ℕ) (p q : Fin m → ℕ) :
    numberNormalization (pairOccupationEquiv m (p,q)) =
      numberNormalization p * numberNormalization q := by
  have hp : (0 : ℝ) ≤ ∏ j, ((p j).factorial : ℝ) :=
    Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
  have hf : (∏ i, (((pairOccupationEquiv m (p,q)) i).factorial : ℝ)) =
      (∏ j, ((p j).factorial : ℝ)) * ∏ j, ((q j).factorial : ℝ) := by
    rw [Fintype.prod_prod_type, Fin.prod_univ_two]
    simp only [pairOccupationEquiv_zero, pairOccupationEquiv_one]
  simp only [numberNormalization, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_ofNat, hf, Real.sqrt_mul hp, div_mul_div_comm,
    ← Real.rpow_add Real.pi_pos]
  congr 2
  ring

/-- The normalized number polynomials factor across the two copies. -/
theorem schrodingerNumberPolynomial_pair (m : ℕ) (p q : Fin m → ℕ) :
    schrodingerNumberPolynomial (pairOccupationEquiv m (p,q)) =
      pairPolynomial m (schrodingerNumberPolynomial p) (schrodingerNumberPolynomial q) := by
  rw [schrodingerNumberPolynomial, numberNormalization_pair, fockNumberPolynomialRaw_pair]
  simp only [schrodingerNumberPolynomial, pairPolynomial, map_smul, smul_mul_smul,
    Complex.ofReal_mul]

/-- The Gaussian representative of a product polynomial is the pointwise product
of the two one-copy representatives. -/
theorem polynomialGaussianFun_pair (m : ℕ) (p q : MvPolynomial (Fin m) ℂ)
    (z : BosonConfig m) :
    polynomialGaussianFun (pairPolynomial m p q) z =
      polynomialGaussianFun p (bosonPosition 0 z) *
        polynomialGaussianFun q (bosonPosition 1 z) := by
  have hn : ‖z‖ ^ 2 = ‖bosonPosition 0 z‖ ^ 2 + ‖bosonPosition 1 z‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
      bosonPosition_apply]
  simp only [polynomialGaussianFun, pairPolynomial, map_mul, eval_rename_prod_mk]
  rw [hn]
  have he : Real.exp (-(‖bosonPosition 0 z‖ ^ 2 + ‖bosonPosition 1 z‖ ^ 2) / 2) =
      Real.exp (-‖bosonPosition 0 z‖ ^ 2 / 2) * Real.exp (-‖bosonPosition 1 z‖ ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Complex.ofReal_mul]
  simp only [bosonPosition]
  ring

/-- Polynomial Gaussian tensor products agree with actual products of wavefunctions. -/
theorem polynomialGaussian_pair (m : ℕ) (p q : MvPolynomial (Fin m) ℂ) :
    polynomialGaussian (pairPolynomial m p q) =
      waveTensor m (hilbertTmul (polynomialGaussian p) (polynomialGaussian q)) := by
  apply Lp.ext
  have h0 := (Measure.quasiMeasurePreserving_fst.comp
    (bosonPositions_measurePreserving m).quasiMeasurePreserving).ae
      (polynomialGaussian_coeFn p)
  have h1 := (Measure.quasiMeasurePreserving_snd.comp
    (bosonPositions_measurePreserving m).quasiMeasurePreserving).ae
      (polynomialGaussian_coeFn q)
  filter_upwards [polynomialGaussian_coeFn (pairPolynomial m p q),
    waveTensor_tmul_coeFn m (polynomialGaussian p) (polynomialGaussian q), h0, h1]
    with z hz ht hp hq
  change polynomialGaussian p (bosonPosition 0 z) =
    polynomialGaussianFun p (bosonPosition 0 z) at hp
  change polynomialGaussian q (bosonPosition 1 z) =
    polynomialGaussianFun q (bosonPosition 1 z) at hq
  rw [hz, ht, hp, hq, polynomialGaussianFun_pair]

/-- A paired number vector is exactly the tensor product of its one-copy number vectors. -/
theorem schrodingerNumberVector_pair (m : ℕ) (p q : Fin m → ℕ) :
    schrodingerNumberVector (pairOccupationEquiv m (p,q)) =
      waveTensor m (hilbertTmul (schrodingerNumberVector p) (schrodingerNumberVector q)) := by
  calc
    _ = polynomialGaussian
        (schrodingerNumberPolynomial (pairOccupationEquiv m (p,q))) :=
      (polynomialGaussian_schrodingerNumberPolynomial _).symm
    _ = polynomialGaussian
        (pairPolynomial m (schrodingerNumberPolynomial p) (schrodingerNumberPolynomial q)) := by
      rw [schrodingerNumberPolynomial_pair]
    _ = _ := by
      simpa only [polynomialGaussian_schrodingerNumberPolynomial p,
        polynomialGaussian_schrodingerNumberPolynomial q] using
          polynomialGaussian_pair m (schrodingerNumberPolynomial p) (schrodingerNumberPolynomial q)

private theorem bilinear_eq_of_occupation_singles (m : ℕ)
    (B C : FockB m →L[ℂ] FockB m →L[ℂ] SchrodingerSpace m)
    (h : ∀ p q : Fin m → ℕ, B (lp.single 2 p 1) (lp.single 2 q 1) =
      C (lp.single 2 p 1) (lp.single 2 q 1)) : B = C := by
  classical
  have hs (p : Fin m → ℕ) (a : ℂ) :
      lp.single 2 p a = a • (lp.single 2 p 1 : FockB m) := by
    rw [← lp.single_smul]
    simp
  apply lp.ext_continuousLinearMap (by norm_num)
  intro p
  apply ContinuousLinearMap.ext
  intro a
  apply lp.ext_continuousLinearMap (by norm_num)
  intro q
  apply ContinuousLinearMap.ext
  intro b
  change B (lp.single 2 p a) (lp.single 2 q b) = C (lp.single 2 p a) (lp.single 2 q b)
  rw [hs p a, hs q b]
  simp only [map_smul, smul_apply, h]

private theorem tpPair_occupation_single (m : ℕ) (p q : Fin m → ℕ) :
    tpPair (lp.single 2 p (1 : ℂ)) (lp.single 2 q 1) = lp.single 2 (p,q) 1 := by
  classical
  apply lp.ext
  funext r
  by_cases hp : r.1 = p <;> by_cases hq : r.2 = q <;>
    simp [tpPair_apply, lp.single_apply, Pi.single_apply, hp, hq, Prod.ext_iff]

/-- The unitary number-basis identification preserves the manuscript's actual
two-copy tensor product on all completed wavefunctions. -/
theorem fockPairSchrodingerEquiv_tpPair (m : ℕ) (f g : FockB m) :
    fockPairSchrodingerEquiv m (tpPair f g) =
      waveTensor m (hilbertTmul (fockSchrodingerEquiv m f) (fockSchrodingerEquiv m g)) := by
  let coords := hilbertCoords (LinearIsometryEquiv.refl ℂ (FockB m))
    (LinearIsometryEquiv.refl ℂ (FockB m))
  let T := (fockPairSchrodingerEquiv m).toContinuousLinearEquiv.toContinuousLinearMap.comp
    coords.toContinuousLinearEquiv.toContinuousLinearMap
  let B : FockB m →L[ℂ] FockB m →L[ℂ] SchrodingerSpace m :=
    (ContinuousLinearMap.compL ℂ (FockB m) (HilbertSquare (FockB m))
      (SchrodingerSpace m) T).comp hilbertTmul
  let U := (fockSchrodingerEquiv m).toContinuousLinearEquiv.toContinuousLinearMap
  let C : FockB m →L[ℂ] FockB m →L[ℂ] SchrodingerSpace m :=
    (waveProduct m).bilinearComp U U
  have hB (x y : FockB m) : B x y = fockPairSchrodingerEquiv m (tpPair x y) := by
    change fockPairSchrodingerEquiv m (coords (hilbertTmul x y)) = _
    rw [hilbertCoords_tmul]
    rfl
  have hC (x y : FockB m) : C x y =
      waveTensor m (hilbertTmul (fockSchrodingerEquiv m x) (fockSchrodingerEquiv m y)) := rfl
  have he : B = C := bilinear_eq_of_occupation_singles m B C fun p q => by
    exact (hB _ _).trans <|
      (congrArg (fockPairSchrodingerEquiv m) (tpPair_occupation_single m p q)).trans <|
      (fockPairSchrodingerEquiv_single m (p,q)).trans <|
      (schrodingerNumberVector_pair m p q).trans <|
      (congrArg (fun z => waveTensor m z)
        (congrArg₂ (fun x y : WaveSpace m => hilbertTmul x y)
          (fockSchrodingerEquiv_single m p).symm (fockSchrodingerEquiv_single m q).symm)).trans
        (hC _ _).symm
  rw [← hB, ← hC, he]

end
end GaussianTesting
