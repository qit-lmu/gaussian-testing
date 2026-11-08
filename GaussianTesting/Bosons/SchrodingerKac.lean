module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.SchrodingerCubeRotations
public import GaussianTesting.Bosons.SchrodingerRotationProjection
public import GaussianTesting.Bosons.TensorRotationProjection
public import GaussianTesting.Bosons.SchrodingerMeanZeroAcceptance
public import GaussianTesting.Kac.GeneralRepresentation
public import GaussianTesting.GradientFlow.HilbertGradientBound

@[expose] public section

/-!
# The physical bosonic Kac operator

The three pair projections in Theorem 6.4 are the axis-fixed projections of
the actual Schrödinger SO(3) action. Compact-group decomposition therefore
gives the manuscript's spectral bound on the completed tensor cube.
-/

namespace GaussianTesting

open UnitaryRepresentation
open scoped InnerProductSpace

noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] waveCubeEquiv waveTensorEquiv

/-- Transport a unitary representation along a linear isometric equivalence. -/
def transportRepresentation
    {G E F : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (π : G →* F ≃ₗᵢ[ℂ] F) (e : E ≃ₗᵢ[ℂ] F) : G →* E ≃ₗᵢ[ℂ] E where
  toFun g := e.trans ((π g).trans e.symm)
  map_one' := by
    ext v
    change e.symm (π 1 (e v)) = v
    rw [map_one]
    exact e.symm_apply_apply v
  map_mul' g h := by
    ext v
    simp only [map_mul, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.coe_mul,
      Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]

/-- The actual copy-rotation representation transported to the Hilbert tensor cube. -/
def schrodingerCubeRepresentation (m : ℕ) :
    SO3.Group →* HilbertCube (WaveSpace m) ≃ₗᵢ[ℂ] HilbertCube (WaveSpace m) :=
  transportRepresentation (schrodingerSpecialOrthogonalRepresentation m 3) (waveCubeEquiv m)

theorem schrodingerCubeRepresentation_apply (m : ℕ) (g : SO3.Group)
    (v : HilbertCube (WaveSpace m)) :
    schrodingerCubeRepresentation m g v = (waveCubeEquiv m).symm
      (schrodingerSpecialOrthogonalRepresentation m 3 g (waveCubeEquiv m v)) := rfl

/-- The transported physical action is strongly continuous. -/
theorem continuous_schrodingerCubeRepresentation (m : ℕ) (v : HilbertCube (WaveSpace m)) :
    Continuous (fun g => schrodingerCubeRepresentation m g v) :=
  (waveCubeEquiv m).symm.continuous.comp
    (continuous_schrodingerSpecialOrthogonalRepresentation m 3 (waveCubeEquiv m v))

private theorem continuous_transport_apply
    {G E F : Type*} [TopologicalSpace G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (π : G → F ≃ₗᵢ[ℂ] F) (e : E ≃ₗᵢ[ℂ] F)
    (hπ : Continuous (fun p : G × F => π p.1 p.2)) :
    Continuous (fun p : E × G => e.symm (π p.2 (e p.1))) := by
  exact e.symm.continuous.comp (hπ.comp
    (continuous_snd.prodMk (e.continuous.comp continuous_fst)))

theorem continuous_schrodingerCubeRepresentation_apply (m : ℕ) :
    Continuous (fun p : HilbertCube (WaveSpace m) × SO3.Group =>
      schrodingerCubeRepresentation m p.2 p.1) := by
  exact continuous_transport_apply
    (schrodingerSpecialOrthogonalRepresentation m 3) (waveCubeEquiv m)
    (continuous_schrodingerSpecialOrthogonalRepresentation_apply m 3)

theorem schrodingerCubeRepresentation_rotX (m : ℕ) (θ : ℝ)
    (v : HilbertCube (WaveSpace m)) :
    schrodingerCubeRepresentation m (SO3.rotX θ) v =
      threeCopyPair23 (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v := by
  apply (waveCubeEquiv m).injective
  change waveCubeEquiv m ((waveCubeEquiv m).symm _) = _
  exact (waveCubeEquiv m).apply_symm_apply _ |>.trans
    (waveCubeEquiv_pair23_rotation m θ v).symm

theorem schrodingerCubeRepresentation_rotZ (m : ℕ) (θ : ℝ)
    (v : HilbertCube (WaveSpace m)) :
    schrodingerCubeRepresentation m (SO3.rotZ θ) v =
      threeCopyPair12 (schrodingerTensorRotation m θ).toLinearIsometry.toContinuousLinearMap v := by
  apply (waveCubeEquiv m).injective
  change waveCubeEquiv m ((waveCubeEquiv m).symm _) = _
  exact (waveCubeEquiv m).apply_symm_apply _ |>.trans
    (waveCubeEquiv_pair12_rotation m θ v).symm

theorem schrodingerCubeRepresentation_rotY (m : ℕ) (θ : ℝ)
    (v : HilbertCube (WaveSpace m)) :
    schrodingerCubeRepresentation m (SO3.rotY θ) v =
      threeCopyPair13 (schrodingerTensorRotation m (-θ)).toLinearIsometry.toContinuousLinearMap v := by
  apply (waveCubeEquiv m).injective
  change waveCubeEquiv m ((waveCubeEquiv m).symm _) = _
  have h := waveCubeEquiv_pair13_rotation m (-θ) v
  simp only [neg_neg] at h
  exact (waveCubeEquiv m).apply_symm_apply _ |>.trans h.symm

theorem schrodingerCubeRepresentation_axisCycle_inv (m : ℕ)
    (v : HilbertCube (WaveSpace m)) :
    schrodingerCubeRepresentation m SO3.axisCycle⁻¹ v = cubeCycle v := by
  apply (waveCubeEquiv m).injective
  change waveCubeEquiv m ((waveCubeEquiv m).symm _) = _
  exact (waveCubeEquiv m).apply_symm_apply _ |>.trans (waveCubeEquiv_cycle m v).symm

private theorem continuous_action_parameter
    {X G T : Type*} [TopologicalSpace X] [TopologicalSpace G] [TopologicalSpace T]
    (f : X × G → X) (hf : Continuous f) (r : T → G) (hr : Continuous r) :
    Continuous (fun p : X × T => f (p.1, r p.2)) :=
  hf.comp (continuous_fst.prodMk (hr.comp continuous_snd))

/-- The first-axis fixed projector is the physical last-two-copy projection. -/
theorem schrodingerCube_fixedProjection_X (m : ℕ) :
    (fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 0)).starProjection =
      threeCopyPair23 (schrodingerTensorP0 m) := by
  let F := fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 0)
  let R := fun t => schrodingerCubeRepresentation m (SO3.rotX t)
  have hR : Continuous (fun p : HilbertCube (WaveSpace m) × ℝ => R p.2 p.1) :=
    continuous_action_parameter
      (fun p : HilbertCube (WaveSpace m) × SO3.Group => schrodingerCubeRepresentation m p.2 p.1)
      (continuous_schrodingerCubeRepresentation_apply m) SO3.rotX SO3.continuous_rotX
  have htensor (t : ℝ) (a : WaveSpace m) (b : HilbertSquare (WaveSpace m)) :
      R t (hilbertTmul a b) = hilbertTmul a (schrodingerTensorRotation m t b) := by
    exact (schrodingerCubeRepresentation_rotX m t (hilbertTmul a b)).trans
      (hilbertTensorMap_tmul (ContinuousLinearMap.id ℂ (WaveSpace m))
        (schrodingerTensorRotation m t).toLinearIsometry.toContinuousLinearMap a b)
  have hfix (v : HilbertCube (WaveSpace m)) : v ∈ F ↔ ∀ t, R t v = v :=
    SO3.mem_fixedSubspace_axisX (schrodingerCubeRepresentation m) v
  exact tensor_rotation_fixedProjection (A := WaveSpace m) (B := HilbertSquare (WaveSpace m))
    (schrodingerTensorRotation m) (continuous_schrodingerTensorRotation m)
    R hR htensor (schrodingerTensorP0 m) (schrodingerTensorP0_eq_rotationAverage m)
    (schrodingerTensorRotation_P0 m) F hfix


private theorem projection_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : E ≃ₗᵢ[ℂ] E) (U V : Submodule ℂ E) [CompleteSpace U] [CompleteSpace V]
    (hmem : ∀ x, x ∈ U ↔ e x ∈ V) (x : E) :
    V.starProjection (e x) = e (U.starProjection x) := by
  apply V.eq_starProjection_of_mem_of_inner_eq_zero
    ((hmem _).mp (U.starProjection_apply_mem x))
  intro y hy
  have hys : e.symm y ∈ U := (hmem _).mpr (by simpa only [e.apply_symm_apply] using hy)
  calc
    inner ℂ (e x - e (U.starProjection x)) y =
        inner ℂ (e (x - U.starProjection x)) (e (e.symm y)) := by
      rw [map_sub, e.apply_symm_apply]
    _ = inner ℂ (x - U.starProjection x) (e.symm y) := e.inner_map_map _ _
    _ = 0 := U.starProjection_inner_eq_zero x _ hys

private theorem cube_axis_cycle_ZX (m : ℕ) (t : ℝ) (v : HilbertCube (WaveSpace m)) :
    schrodingerCubeRepresentation m (SO3.rotZ t) (cubeCycle v) =
      cubeCycle (schrodingerCubeRepresentation m (SO3.rotX t) v) := by
  calc
    _ = threeCopyPair12
        (schrodingerTensorRotation m t).toLinearIsometry.toContinuousLinearMap (cubeCycle v) :=
      schrodingerCubeRepresentation_rotZ m t _
    _ = cubeCycle (threeCopyPair23
        (schrodingerTensorRotation m t).toLinearIsometry.toContinuousLinearMap v) :=
      threeCopyPair12_cubeCycle _ v
    _ = _ := congrArg cubeCycle (schrodingerCubeRepresentation_rotX m t v).symm

private theorem cube_axis_cycle_XY (m : ℕ) (t : ℝ) (v : HilbertCube (WaveSpace m)) :
    schrodingerCubeRepresentation m (SO3.rotX t) (cubeCycle v) =
      cubeCycle (schrodingerCubeRepresentation m (SO3.rotY t) v) := by
  let π := schrodingerCubeRepresentation m
  have hm (g h : SO3.Group) (x : HilbertCube (WaveSpace m)) : π g (π h x) = π (g*h) x :=
    (congrArg (fun e : HilbertCube (WaveSpace m) ≃ₗᵢ[ℂ] HilbertCube (WaveSpace m) => e x)
      (map_mul π g h)).symm
  have hg : SO3.rotX t * SO3.axisCycle⁻¹ = SO3.axisCycle⁻¹ * SO3.rotY t := by
    have h := SO3.cycleConj_rotX t
    change SO3.axisCycle * SO3.rotX t * SO3.axisCycle⁻¹ = SO3.rotY t at h
    rw [← h]
    group
  calc
    _ = π (SO3.rotX t) (π SO3.axisCycle⁻¹ v) :=
      congrArg (π (SO3.rotX t)) (schrodingerCubeRepresentation_axisCycle_inv m v).symm
    _ = π (SO3.rotX t * SO3.axisCycle⁻¹) v := hm _ _ _
    _ = π (SO3.axisCycle⁻¹ * SO3.rotY t) v := congrArg (fun g => π g v) hg
    _ = π SO3.axisCycle⁻¹ (π (SO3.rotY t) v) := (hm _ _ _).symm
    _ = _ := schrodingerCubeRepresentation_axisCycle_inv m _

private theorem fixedProjection_cycle_ZX (m : ℕ) (v : HilbertCube (WaveSpace m)) :
    (fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 2)).starProjection
      (cubeCycle v) = cubeCycle
        ((fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 0)).starProjection v) := by
  apply projection_transport
  intro x
  simp only [SO3.mem_fixedSubspace_axisX, SO3.mem_fixedSubspace_axisZ]
  constructor
  · intro hx t
    exact (cube_axis_cycle_ZX m t x).trans (congrArg cubeCycle (hx t))
  · intro hx t
    exact cubeCycle.injective ((cube_axis_cycle_ZX m t x).symm.trans (hx t))

private theorem fixedProjection_cycle_XY (m : ℕ) (v : HilbertCube (WaveSpace m)) :
    (fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 0)).starProjection
      (cubeCycle v) = cubeCycle
        ((fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 1)).starProjection v) := by
  apply projection_transport
  intro x
  simp only [SO3.mem_fixedSubspace_axisY, SO3.mem_fixedSubspace_axisX]
  constructor
  · intro hx t
    exact (cube_axis_cycle_XY m t x).trans (congrArg cubeCycle (hx t))
  · intro hx t
    exact cubeCycle.injective ((cube_axis_cycle_XY m t x).symm.trans (hx t))

/-- The third-axis fixed projector is the physical first-two-copy projection. -/
theorem schrodingerCube_fixedProjection_Z (m : ℕ) :
    (fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 2)).starProjection =
      threeCopyPair12 (schrodingerTensorP0 m) := by
  ext v : 1
  let w := (cubeCycle (H := WaveSpace m)).symm v
  have hw : cubeCycle w = v := cubeCycle.apply_symm_apply v
  calc
    _ = (fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 2)).starProjection
        (cubeCycle w) := congrArg _ hw.symm
    _ = cubeCycle ((fixedSubspace (schrodingerCubeRepresentation m)
        (SO3.axisSubgroups 0)).starProjection w) := fixedProjection_cycle_ZX m w
    _ = cubeCycle (threeCopyPair23 (schrodingerTensorP0 m) w) :=
      congrArg (fun P : HilbertCube (WaveSpace m) →L[ℂ] HilbertCube (WaveSpace m) =>
        cubeCycle (P w)) (schrodingerCube_fixedProjection_X m)
    _ = threeCopyPair12 (schrodingerTensorP0 m) (cubeCycle w) :=
      (threeCopyPair12_cubeCycle _ w).symm
    _ = _ := congrArg _ hw

/-- The second-axis fixed projector is the physical first-and-third-copy projection. -/
theorem schrodingerCube_fixedProjection_Y (m : ℕ) :
    (fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 1)).starProjection =
      threeCopyPair13 (schrodingerTensorP0 m) := by
  have hs : hilbertSwap.conjStarAlgEquiv (schrodingerTensorP0 m) = schrodingerTensorP0 m := by
    ext w
    change hilbertSwap (schrodingerTensorP0 m (hilbertSwap.symm w)) = schrodingerTensorP0 m w
    exact ((schrodingerTensorP0_isAcceptance m).swap_comm (hilbertSwap.symm w)).symm.trans
      (congrArg (schrodingerTensorP0 m)
        ((hilbertSwap (E := WaveSpace m) (F := WaveSpace m)).apply_symm_apply w))
  ext v : 1
  apply cubeCycle.injective
  calc
    _ = (fixedSubspace (schrodingerCubeRepresentation m) (SO3.axisSubgroups 0)).starProjection
        (cubeCycle v) := (fixedProjection_cycle_XY m v).symm
    _ = threeCopyPair23 (schrodingerTensorP0 m) (cubeCycle v) :=
      DFunLike.congr_fun (schrodingerCube_fixedProjection_X m) _
    _ = cubeCycle (threeCopyPair13 (schrodingerTensorP0 m) v) := by
      change threeCopyPair23 (schrodingerTensorP0 m) (cubeCycle v) =
        cubeCycle (cubeCycle.symm (threeCopyPair23
          (hilbertSwap.conjStarAlgEquiv (schrodingerTensorP0 m)) (cubeCycle v)))
      exact (congrArg (fun P => threeCopyPair23 P (cubeCycle v)) hs).symm.trans
        (cubeCycle.apply_symm_apply _).symm

/-- The manuscript's physical three-copy average is exactly its Kac operator. -/
theorem schrodinger_threeCopyAverage_eq_kacAverage (m : ℕ) :
    threeCopyAverage (H := WaveSpace m) (schrodingerTensorP0 m) = SO3.kacAverage (schrodingerCubeRepresentation m) := by
  have hsum := congrArg₂ (fun A B : HilbertCube (WaveSpace m) →L[ℂ] HilbertCube (WaveSpace m) => A + B)
    (congrArg₂ (fun A B : HilbertCube (WaveSpace m) →L[ℂ] HilbertCube (WaveSpace m) => A + B)
      (schrodingerCube_fixedProjection_X m) (schrodingerCube_fixedProjection_Y m))
    (schrodingerCube_fixedProjection_Z m)
  have hperm : threeCopyPair12 (schrodingerTensorP0 m) + threeCopyPair13 (schrodingerTensorP0 m) +
      threeCopyPair23 (schrodingerTensorP0 m) =
      threeCopyPair23 (schrodingerTensorP0 m) + threeCopyPair13 (schrodingerTensorP0 m) +
        threeCopyPair12 (schrodingerTensorP0 m) := by abel
  exact congrArg (fun P : HilbertCube (WaveSpace m) →L[ℂ] HilbertCube (WaveSpace m) =>
    (3 : ℂ)⁻¹ • P) (hperm.trans hsum.symm)

/-- **Theorem 6.4, spectral step.** The physical mean-zero three-copy operator
has spectrum contained in `[0,7/12] ∪ {1}`. -/
theorem schrodinger_meanZero_spectrum_subset (m : ℕ) :
    spectrum ℂ (threeCopyAverage (H := WaveSpace m) (schrodingerTensorP0 m)) ⊆
      Complex.ofReal '' Set.Icc 0 (7 / 12 : ℝ) ∪ {1} := by
  have hspec := SO3.kacAverage_spectrum_subset (E := HilbertCube (WaveSpace m))
    (schrodingerCubeRepresentation m)
    (continuous_schrodingerCubeRepresentation m)
  intro z hz
  apply hspec
  exact Eq.mp (congrArg (fun P : HilbertCube (WaveSpace m) →L[ℂ] HilbertCube (WaveSpace m) =>
    z ∈ spectrum ℂ P) (schrodinger_threeCopyAverage_eq_kacAverage m)) hz

end
end GaussianTesting
