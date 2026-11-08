module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.SecondQuantization
public import GaussianTesting.Fermions.PairGenerator

@[expose] public section

/-!
# Rotating the two sets of fermionic modes

The one-particle action following Eq. (5.5) is `R ⊗ I_m`, indexed copy first.
-/

namespace GaussianTesting

noncomputable section

open Matrix
open scoped Kronecker

def pairModeMatrix (m : ℕ) (R : FermionModeRotation 2) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (R.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ))

/-- The one-particle copy rotation `R ⊗ I_m`. -/
def fermionPairModeRotation (m : ℕ) : FermionModeRotation 2 →* FermionModeRotation (2 * m) where
  toFun R := ⟨pairModeMatrix m R, by
    refine Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩
    · apply (Matrix.mem_orthogonalGroup_iff' _ _).mpr
      have hR := (Matrix.mem_orthogonalGroup_iff' _ _).mp R.property.1
      have ht : (R.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ))ᵀ =
          R.valᵀ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℝ) := by
        ext; simp [Matrix.one_apply, eq_comm]
      simp only [pairModeMatrix, Matrix.reindex_apply, Matrix.transpose_submatrix]
      rw [Matrix.submatrix_mul_equiv, ht, ← Matrix.mul_kronecker_mul,
        hR, one_mul, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
    · have hd : R.val.det = 1 := R.property.2
      rw [pairModeMatrix, Matrix.det_reindex_self, Matrix.det_kronecker,
        hd, Matrix.det_one]
      simp⟩
  map_one' := by
    apply Subtype.ext
    simp [pairModeMatrix]
  map_mul' R S := by
    apply Subtype.ext
    change pairModeMatrix m (R * S) = pairModeMatrix m R * pairModeMatrix m S
    simp only [pairModeMatrix, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    congr 1
    simpa using Matrix.mul_kronecker_mul R.val S.val
      (1 : Matrix (Fin m) (Fin m) ℝ) (1 : Matrix (Fin m) (Fin m) ℝ)

@[simp] theorem fermionPairModeRotation_apply (m : ℕ) (R : FermionModeRotation 2)
    (a b : Fin 2) (k l : Fin m) :
    (fermionPairModeRotation m R).val (finProdFinEquiv (a, k)) (finProdFinEquiv (b, l)) =
      if k = l then R.val a b else 0 := by
  simp [fermionPairModeRotation, pairModeMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The copy-mode embedding is continuous in the matrix topology. -/
theorem continuous_fermionPairModeRotation (m : ℕ) : Continuous (fermionPairModeRotation m) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun R : FermionModeRotation 2 =>
    R.val (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      (1 : Matrix (Fin m) (Fin m) ℝ) (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2)
  have hc : Continuous (fun R : FermionModeRotation 2 =>
      R.val (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1) := by
    exact (continuous_apply (finProdFinEquiv.symm j).1).comp
      ((continuous_apply (finProdFinEquiv.symm i).1).comp continuous_subtype_val)
  exact hc.mul continuous_const

variable {m : ℕ}

/-- The manuscript's copy-rotation representation on `H_m^⊗2`. -/
def fermionPairRepresentation (m : ℕ) : FermionModeRotation 2 →* (H2 (Qm m) ≃ₗᵢ[ℂ] H2 (Qm m)) where
  toFun R := ((fermionPairEquiv m).symm.trans
    (fermionSecondQuantization (fermionPairModeRotation m R))).trans (fermionPairEquiv m)
  map_one' := by ext ψ; simp
  map_mul' R S := by ext ψ; simp

@[simp] theorem fermionPairRepresentation_apply (R : FermionModeRotation 2) (ψ : H2 (Qm m)) :
    fermionPairRepresentation m R ψ = fermionPairEquiv m
      (fermionSecondQuantization (fermionPairModeRotation m R) ((fermionPairEquiv m).symm ψ)) := rfl

/-- The two-copy second-quantized action is strongly continuous. -/
theorem continuous_fermionPairRepresentation_orbit (ψ : H2 (Qm m)) :
    Continuous (fun R => fermionPairRepresentation m R ψ) :=
  (fermionPairEquiv m).continuous.comp
    ((continuous_fermionSecondQuantization_orbit ((fermionPairEquiv m).symm ψ)).comp
      (continuous_fermionPairModeRotation m))

/-- Second quantization fixes the empty occupation state on all copies. -/
theorem fermionPairRepresentation_vacuum (R : FermionModeRotation 2) :
    fermionPairRepresentation m R
      (tp2 (fermionVacuum m) (fermionVacuum m)) =
      tp2 (fermionVacuum m) (fermionVacuum m) := by
  have hv : fermionPairEquiv m (fermionVacuum (2 * m)) =
      tp2 (fermionVacuum m) (fermionVacuum m) :=
    fermionPairEquiv_vacuum
  rw [← hv, fermionPairRepresentation_apply, LinearIsometryEquiv.symm_apply_apply,
    fermionSecondQuantization_vacuum]

/-- Copy rotations rotate the two parity-string Majoranas by the columns
of the one-particle rotation, as in the manuscript's proof. -/
theorem fermionPairRepresentation_majorana (R : FermionModeRotation 2) (a : Fin 2)
    (b : Fin m × Bool) (ψ : H2 (Qm m)) :
    fermionPairRepresentation m R (fermionPairMajorana a b ψ) =
      ∑ c, (R.val c a : ℂ) • fermionPairMajorana c b (fermionPairRepresentation m R ψ) := by
  classical
  have hm (a : Fin 2) (b : Fin m × Bool) (φ : HF (2 * m)) :
      fermionPairEquiv m (maj (fermionPairCopyMode a b.1, b.2) φ) =
        fermionPairMajorana a b (fermionPairEquiv m φ) :=
    fermionPairEquiv_majorana a b φ
  have h := (fermionSecondQuantization_implements (fermionPairModeRotation m R)).passive_majorana
    (fermionPairCopyMode a b.1) b.2 ((fermionPairEquiv m).symm ψ)
  apply_fun fermionPairEquiv m at h
  have ht := hm a b ((fermionPairEquiv m).symm ψ)
  rw [LinearIsometryEquiv.apply_symm_apply] at ht
  have ht' : (fermionPairEquiv m).symm (fermionPairMajorana a b ψ) =
      maj (fermionPairCopyMode a b.1, b.2) ((fermionPairEquiv m).symm ψ) := by
    rw [← ht, LinearIsometryEquiv.symm_apply_apply]
  rw [fermionPairRepresentation_apply, ht', h]
  simp only [map_sum, map_smul]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin m ≃ Fin (2 * m))]
  simp only [Fintype.sum_prod_type]
  simp only [fermionPairCopyMode, fermionPairModeRotation_apply, apply_ite,
    Complex.ofReal_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact Finset.sum_congr rfl (fun c _ => congrArg ((R.val c a : ℂ) • ·)
    (hm c b _))

end
end GaussianTesting
