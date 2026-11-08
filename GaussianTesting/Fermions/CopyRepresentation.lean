module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Fermions.CopyCoordinates
public import GaussianTesting.Fermions.CopyModeRotation

@[expose] public section

/-!
# The second-quantized SO(3) action on three fermionic copies

This is the representation `Γ∧(R ⊗ I_m)` used in the proof of Theorem 5.2,
transported through the occupation-coordinate tensor identification.
-/

namespace GaussianTesting

noncomputable section

variable {m : ℕ}

/-- The manuscript's copy-rotation representation on `H_m^⊗3`. -/
def fermionCopyRepresentation (m : ℕ) : SO3.Group →* (H3 (Qm m) ≃ₗᵢ[ℂ] H3 (Qm m)) where
  toFun R := ((fermionTripleEquiv m).symm.trans
    (fermionSecondQuantization (fermionCopyModeRotation m R))).trans (fermionTripleEquiv m)
  map_one' := by ext ψ; simp
  map_mul' R S := by ext ψ; simp

@[simp] theorem fermionCopyRepresentation_apply (R : SO3.Group) (ψ : H3 (Qm m)) :
    fermionCopyRepresentation m R ψ = fermionTripleEquiv m
      (fermionSecondQuantization (fermionCopyModeRotation m R) ((fermionTripleEquiv m).symm ψ)) := rfl

/-- The three-copy second-quantized action is strongly continuous. -/
theorem continuous_fermionCopyRepresentation_orbit (ψ : H3 (Qm m)) :
    Continuous (fun R => fermionCopyRepresentation m R ψ) :=
  (fermionTripleEquiv m).continuous.comp
    ((continuous_fermionSecondQuantization_orbit ((fermionTripleEquiv m).symm ψ)).comp
      (continuous_fermionCopyModeRotation m))

/-- Second quantization fixes the empty occupation state on all copies. -/
theorem fermionCopyRepresentation_vacuum (R : SO3.Group) :
    fermionCopyRepresentation m R
      (tp3 (fermionVacuum m) (fermionVacuum m) (fermionVacuum m)) =
      tp3 (fermionVacuum m) (fermionVacuum m) (fermionVacuum m) := by
  have hv : fermionTripleEquiv m (fermionVacuum (3 * m)) =
      tp3 (fermionVacuum m) (fermionVacuum m) (fermionVacuum m) :=
    fermionTripleEquiv_vacuum
  rw [← hv, fermionCopyRepresentation_apply, LinearIsometryEquiv.symm_apply_apply,
    fermionSecondQuantization_vacuum]

/-- Copy rotations rotate the three parity-string Majoranas by the columns
of the one-particle rotation, as in the manuscript's proof. -/
theorem fermionCopyRepresentation_majorana (R : SO3.Group) (a : Fin 3)
    (b : Fin m × Bool) (ψ : H3 (Qm m)) :
    fermionCopyRepresentation m R (fermionCubeMajorana a b ψ) =
      ∑ c, (R.val c a : ℂ) • fermionCubeMajorana c b (fermionCopyRepresentation m R ψ) := by
  classical
  have hm (a : Fin 3) (b : Fin m × Bool) (φ : HF (3 * m)) :
      fermionTripleEquiv m (maj (fermionCopyMode a b.1, b.2) φ) =
        fermionCubeMajorana a b (fermionTripleEquiv m φ) :=
    fermionTripleEquiv_majorana a b φ
  have h := (fermionSecondQuantization_implements (fermionCopyModeRotation m R)).passive_majorana
    (fermionCopyMode a b.1) b.2 ((fermionTripleEquiv m).symm ψ)
  apply_fun fermionTripleEquiv m at h
  have ht := hm a b ((fermionTripleEquiv m).symm ψ)
  rw [LinearIsometryEquiv.apply_symm_apply] at ht
  have ht' : (fermionTripleEquiv m).symm (fermionCubeMajorana a b ψ) =
      maj (fermionCopyMode a b.1, b.2) ((fermionTripleEquiv m).symm ψ) := by
    rw [← ht, LinearIsometryEquiv.symm_apply_apply]
  rw [fermionCopyRepresentation_apply, ht', h]
  simp only [map_sum, map_smul]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 3 × Fin m ≃ Fin (3 * m))]
  simp only [Fintype.sum_prod_type]
  simp only [fermionCopyMode, fermionCopyModeRotation_apply, apply_ite,
    Complex.ofReal_zero, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact Finset.sum_congr rfl (fun c _ => congrArg ((R.val c a : ℂ) • ·)
    (hm c b _))

end
end GaussianTesting
