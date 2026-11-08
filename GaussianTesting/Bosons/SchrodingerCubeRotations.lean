module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerCube
public import GaussianTesting.Bosons.SchrodingerFourCopy
public import GaussianTesting.Bosons.SchrodingerCircuitSwap
public import GaussianTesting.GradientFlow.HilbertPairOperators
public import GaussianTesting.Kac.SO3Cyclic

@[expose] public section

/-!
# Pair rotations on the physical tensor cube

The three pairwise rotations of Theorem 6.4 agree with the coordinate-axis
SO(3) action under the canonical wavefunction identification.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace TensorProduct

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 2048

/-- The cyclic permutation sends the three tensor factors to the order 2,3,1. -/
def cubeCycle {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    HilbertCube H ≃ₗᵢ[ℂ] HilbertCube H := hilbertSwap.trans hilbertAssoc

@[simp] theorem cubeCycle_tmul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y z : H) :
    cubeCycle (hilbertTmul x (hilbertTmul y z)) = hilbertTmul y (hilbertTmul z x) := by
  simp [cubeCycle]

private theorem cubePosition_axisCycle_inv (m : ℕ) (i : Fin 3) (z : CopiesConfig m 3) :
    cubePosition i (copiesCoordinateMap
      ((specialOrthogonalCopiesInclusion 3 SO3.axisCycle⁻¹)⁻¹ :
        Matrix.orthogonalGroup (Fin 3) ℝ) z) = cubePosition (i + 2) z := by
  simp only [map_inv, inv_inv]
  change cubePosition i (copiesCoordinateMap
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ) z) = _
  ext j
  fin_cases i <;> simp [copiesCoordinateMap_apply, Fin.sum_univ_succ]

/-- The tensor cycle is the inverse coordinate-axis cycle in the physical action. -/
theorem waveCubeEquiv_cycle (m : ℕ) (v : HilbertCube (WaveSpace m)) :
    waveCubeEquiv m (cubeCycle v) =
      schrodingerSpecialOrthogonalRepresentation m 3 SO3.axisCycle⁻¹ (waveCubeEquiv m v) := by
  have he : (waveCubeEquiv m).toLinearIsometry.toContinuousLinearMap.comp
      cubeCycle.toLinearIsometry.toContinuousLinearMap =
      (schrodingerSpecialOrthogonalRepresentation m 3 SO3.axisCycle⁻¹).toLinearIsometry.toContinuousLinearMap.comp
        (waveCubeEquiv m).toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on dense_span_hilbertTriple
    rintro _ ⟨⟨f,g,h⟩,rfl⟩
    change waveCubeEquiv m (cubeCycle (hilbertTmul f (hilbertTmul g h))) = _
    refine (congrArg (waveCubeEquiv m) (cubeCycle_tmul f g h)).trans ?_
    apply Lp.ext
    let O := specialOrthogonalCopiesInclusion 3 SO3.axisCycle⁻¹
    filter_upwards [waveCubeEquiv_triple_coeFn m g h f,
      schrodingerCopiesAction_coeFn m 3 O (waveCubeEquiv m (hilbertTmul f (hilbertTmul g h))),
      (copiesCoordinateMap_measurePreserving m 3 O⁻¹).quasiMeasurePreserving.ae_eq_comp
        (waveCubeEquiv_triple_coeFn m f g h)] with z hleft hright hpull
    exact hleft.trans (hright.trans (hpull.trans (by
      simp only [Function.comp_apply, O, cubePosition_axisCycle_inv]
      change f (cubePosition 2 z) * (g (cubePosition 0 z) * h (cubePosition 1 z)) = _
      ring))).symm
  exact DFunLike.congr_fun he v

/-- Cyclic permutation moves the last-two pair operator to the first two factors. -/
theorem threeCopyPair12_cubeCycle {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : HilbertSquare H →L[ℂ] HilbertSquare H) (v : HilbertCube H) :
    threeCopyPair12 P (cubeCycle v) = cubeCycle (threeCopyPair23 P v) := by
  have he : (threeCopyPair12 P).comp cubeCycle.toLinearIsometry.toContinuousLinearMap =
      cubeCycle.toLinearIsometry.toContinuousLinearMap.comp (threeCopyPair23 P) := by
    apply hilbertTensor_ext
    intro x w
    simp [cubeCycle, threeCopyPair12, threeCopyPair23]
  exact DFunLike.congr_fun he v

private theorem cubePosition_rotX (m : ℕ) (θ : ℝ) (z : CopiesConfig m 3) :
    cubePosition 0 (copiesCoordinateMap
      ((specialOrthogonalCopiesInclusion 3 (SO3.rotX θ))⁻¹ :
        Matrix.orthogonalGroup (Fin 3) ℝ) z) = cubePosition 0 z := by
  ext j
  simp [copiesCoordinateMap_apply, specialOrthogonalCopiesInclusion, SO3.rotX,
    SO3.rotXMatrix, Matrix.star_eq_conjTranspose,
    Fin.sum_univ_succ]

private theorem cubeTail_rotX (m : ℕ) (θ : ℝ) (z : CopiesConfig m 3) :
    cubeTail (copiesCoordinateMap
      ((specialOrthogonalCopiesInclusion 3 (SO3.rotX θ))⁻¹ :
        Matrix.orthogonalGroup (Fin 3) ℝ) z) = bosonRotate θ (cubeTail z) := by
  ext ⟨i,j⟩
  fin_cases i <;>
    simp [copiesCoordinateMap_apply, specialOrthogonalCopiesInclusion, SO3.rotX,
      SO3.rotXMatrix, Matrix.star_eq_conjTranspose,
      Fin.sum_univ_succ]

/-- Rotating the last two tensor factors is the first-axis SO(3) action. -/
theorem waveCubeEquiv_pair23_rotation (m : ℕ) (θ : ℝ) (v : HilbertCube (WaveSpace m)) :
    waveCubeEquiv m (threeCopyPair23
      (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v) =
    schrodingerSpecialOrthogonalRepresentation m 3 (SO3.rotX θ) (waveCubeEquiv m v) := by
  apply hilbertTensor_induction (p := fun v =>
    waveCubeEquiv m (threeCopyPair23
      (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v) =
    schrodingerSpecialOrthogonalRepresentation m 3 (SO3.rotX θ) (waveCubeEquiv m v))
  · exact isClosed_eq
      ((waveCubeEquiv m).continuous.comp (threeCopyPair23 _).continuous)
      ((schrodingerSpecialOrthogonalRepresentation m 3 (SO3.rotX θ)).continuous.comp
        (waveCubeEquiv m).continuous)
  · intro f w
    simp only [threeCopyPair23, hilbertTensorMap_tmul, ContinuousLinearMap.id_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    apply Lp.ext
    have htail : QuasiMeasurePreserving (cubeTail (m := m)) volume volume :=
      quasiMeasurePreserving_snd.comp (cubePositions_measurePreserving m).quasiMeasurePreserving
    let O := specialOrthogonalCopiesInclusion 3 (SO3.rotX θ)
    filter_upwards [waveCubeEquiv_tmul_coeFn m f (schrodingerTensorRotation m θ w),
      htail.ae_eq_comp (schrodingerRotation_coeFn m θ (waveTensorEquiv m w)),
      schrodingerCopiesAction_coeFn m 3 O (waveCubeEquiv m (hilbertTmul f w)),
      (copiesCoordinateMap_measurePreserving m 3 O⁻¹).quasiMeasurePreserving.ae_eq_comp
        (waveCubeEquiv_tmul_coeFn m f w)] with z hleft hrot hright hpull
    have he : waveTensorEquiv m (schrodingerTensorRotation m θ w) =
        schrodingerRotation m θ (waveTensorEquiv m w) := by
      change waveTensorEquiv m ((waveTensorEquiv m).symm
        (schrodingerRotation m θ (waveTensorEquiv m w))) = _
      exact (waveTensorEquiv m).apply_symm_apply _
    refine hleft.trans ?_
    calc
      _ = f (cubePosition 0 z) * schrodingerRotation m θ (waveTensorEquiv m w) (cubeTail z) :=
        congrArg (fun F : SchrodingerSpace m => f (cubePosition 0 z) * F (cubeTail z)) he
      _ = f (cubePosition 0 z) * waveTensorEquiv m w (bosonRotate θ (cubeTail z)) :=
        congrArg (fun a => f (cubePosition 0 z) * a) hrot
      _ = _ := (hright.trans (hpull.trans (by
        dsimp only [Function.comp_apply, O]
        rw [cubePosition_rotX, cubeTail_rotX]))).symm
  · intro u v hu hv
    simp only [map_add, hu, hv]

/-- Rotating the first two tensor factors is the third-axis SO(3) action. -/
theorem waveCubeEquiv_pair12_rotation (m : ℕ) (θ : ℝ) (v : HilbertCube (WaveSpace m)) :
    waveCubeEquiv m (threeCopyPair12
      (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v) =
    schrodingerSpecialOrthogonalRepresentation m 3 (SO3.rotZ θ) (waveCubeEquiv m v) := by
  let w := (cubeCycle (H := WaveSpace m)).symm v
  have hw : cubeCycle w = v := cubeCycle.apply_symm_apply v
  have hg : SO3.axisCycle⁻¹ * SO3.rotX θ = SO3.rotZ θ * SO3.axisCycle⁻¹ := by
    have h := SO3.cycleConj_rotZ θ
    change SO3.axisCycle * SO3.rotZ θ * SO3.axisCycle⁻¹ = SO3.rotX θ at h
    rw [← h]
    group
  let π := schrodingerSpecialOrthogonalRepresentation m 3
  have hm (g h : SO3.Group) (x : CopiesWaveSpace m 3) : π g (π h x) = π (g*h) x :=
    (congrArg (fun e : CopiesWaveSpace m 3 ≃ₗᵢ[ℂ] CopiesWaveSpace m 3 => e x)
      (map_mul π g h)).symm
  calc
    _ = waveCubeEquiv m (threeCopyPair12
        (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap (cubeCycle w)) :=
      congrArg (fun z => waveCubeEquiv m (threeCopyPair12
        (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap z)) hw.symm
    _ = waveCubeEquiv m (cubeCycle (threeCopyPair23
        (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap w)) :=
      congrArg (waveCubeEquiv m) (threeCopyPair12_cubeCycle _ w)
    _ = π SO3.axisCycle⁻¹ (waveCubeEquiv m (threeCopyPair23
        (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap w)) :=
      waveCubeEquiv_cycle m _
    _ = π SO3.axisCycle⁻¹ (π (SO3.rotX θ) (waveCubeEquiv m w)) :=
      congrArg (π SO3.axisCycle⁻¹) (waveCubeEquiv_pair23_rotation m θ w)
    _ = π (SO3.axisCycle⁻¹ * SO3.rotX θ) (waveCubeEquiv m w) := hm _ _ _
    _ = π (SO3.rotZ θ * SO3.axisCycle⁻¹) (waveCubeEquiv m w) :=
      congrArg (fun g => π g (waveCubeEquiv m w)) hg
    _ = π (SO3.rotZ θ) (π SO3.axisCycle⁻¹ (waveCubeEquiv m w)) := (hm _ _ _).symm
    _ = π (SO3.rotZ θ) (waveCubeEquiv m (cubeCycle w)) :=
      congrArg (π (SO3.rotZ θ)) (waveCubeEquiv_cycle m w).symm
    _ = _ := congrArg (fun z => π (SO3.rotZ θ) (waveCubeEquiv m z)) hw

/-- The first-and-third pair orientation gives the negative second-axis angle. -/
theorem waveCubeEquiv_pair13_rotation (m : ℕ) (θ : ℝ) (v : HilbertCube (WaveSpace m)) :
    waveCubeEquiv m (threeCopyPair13
      (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v) =
    schrodingerSpecialOrthogonalRepresentation m 3 (SO3.rotY (-θ)) (waveCubeEquiv m v) := by
  have hs : hilbertSwap.conjStarAlgEquiv
      (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap =
      (schrodingerTensorRotation m (-θ)).toLinearIsometry.toContinuousLinearMap := by
    ext w
    change hilbertSwap (schrodingerTensorRotation m θ (hilbertSwap.symm w)) =
      schrodingerTensorRotation m (-θ) w
    exact (schrodingerTensorRotation_swap m θ _).trans
      (congrArg (schrodingerTensorRotation m (-θ))
        ((hilbertSwap (E := WaveSpace m) (F := WaveSpace m)).apply_symm_apply w))
  have ht : cubeCycle (threeCopyPair13
      (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v) =
      threeCopyPair23 (schrodingerTensorRotation m (-θ)).toLinearIsometry.toContinuousLinearMap
        (cubeCycle v) := by
    change cubeCycle (cubeCycle.symm (threeCopyPair23
      (hilbertSwap.conjStarAlgEquiv
        (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap) (cubeCycle v))) = _
    exact cubeCycle.apply_symm_apply _ |>.trans
      (congrArg (fun P => threeCopyPair23 P (cubeCycle v)) hs)
  have hg : SO3.rotX (-θ) * SO3.axisCycle⁻¹ = SO3.axisCycle⁻¹ * SO3.rotY (-θ) := by
    have h := SO3.cycleConj_rotX (-θ)
    change SO3.axisCycle * SO3.rotX (-θ) * SO3.axisCycle⁻¹ = SO3.rotY (-θ) at h
    rw [← h]
    group
  let π := schrodingerSpecialOrthogonalRepresentation m 3
  have hm (g h : SO3.Group) (x : CopiesWaveSpace m 3) : π g (π h x) = π (g*h) x :=
    (congrArg (fun e : CopiesWaveSpace m 3 ≃ₗᵢ[ℂ] CopiesWaveSpace m 3 => e x)
      (map_mul π g h)).symm
  apply (π SO3.axisCycle⁻¹).injective
  calc
    _ = waveCubeEquiv m (cubeCycle (threeCopyPair13
        (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v)) :=
      (waveCubeEquiv_cycle m _).symm
    _ = waveCubeEquiv m (threeCopyPair23
        (schrodingerTensorRotation m (-θ)).toLinearIsometry.toContinuousLinearMap (cubeCycle v)) :=
      congrArg (waveCubeEquiv m) ht
    _ = π (SO3.rotX (-θ)) (waveCubeEquiv m (cubeCycle v)) :=
      waveCubeEquiv_pair23_rotation m (-θ) (cubeCycle v)
    _ = π (SO3.rotX (-θ)) (π SO3.axisCycle⁻¹ (waveCubeEquiv m v)) :=
      congrArg (π (SO3.rotX (-θ))) (waveCubeEquiv_cycle m v)
    _ = π (SO3.rotX (-θ) * SO3.axisCycle⁻¹) (waveCubeEquiv m v) := hm _ _ _
    _ = π (SO3.axisCycle⁻¹ * SO3.rotY (-θ)) (waveCubeEquiv m v) :=
      congrArg (fun g => π g (waveCubeEquiv m v)) hg
    _ = _ := (hm _ _ _).symm

end
end GaussianTesting
