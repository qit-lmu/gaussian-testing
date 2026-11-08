module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.ProductLpTensor
public import GaussianTesting.Bosons.SchrodingerTensorUnitary
public import GaussianTesting.Bosons.SchrodingerCopies
public import GaussianTesting.Kac.SO3Rotations

@[expose] public section

/-!
# The physical Schrödinger tensor cube

The three-copy Hilbert tensor product is identified with the actual L²
wavefunctions on three sets of position coordinates, as in Theorem 6.4.
-/

namespace GaussianTesting

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace TensorProduct

noncomputable section

set_option maxHeartbeats 600000

/-- Position coordinates of one copy in the three-copy space. -/
def cubePosition {m : ℕ} (i : Fin 3) (z : CopiesConfig m 3) : WaveConfig m :=
  WithLp.toLp 2 fun j => z (i, j)

/-- Position coordinates of the last two copies. -/
def cubeTail {m : ℕ} (z : CopiesConfig m 3) : BosonConfig m :=
  WithLp.toLp 2 fun p => z (p.1.succ, p.2)

@[simp] theorem cubePosition_apply {m : ℕ} (i : Fin 3) (z : CopiesConfig m 3) (j : Fin m) :
    cubePosition i z j = z (i,j) := rfl

@[simp] theorem cubeTail_apply {m : ℕ} (z : CopiesConfig m 3) (i : Fin 2) (j : Fin m) :
    cubeTail z (i,j) = z (i.succ,j) := rfl

/-- Split the first copy from the last two in the position configuration. -/
def splitCubeConfig (m : ℕ) :
    CopiesConfig m 3 ≃ₗ[ℝ] WithLp 2 (WaveConfig m × BosonConfig m) where
  toFun z := WithLp.toLp 2 (cubePosition 0 z, cubeTail z)
  invFun xy := WithLp.toLp 2 fun p =>
    Fin.cases (xy.fst p.2) (fun i : Fin 2 => xy.snd (i,p.2)) p.1
  left_inv z := by
    ext ⟨i,j⟩
    fin_cases i <;> rfl
  right_inv xy := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · ext j; rfl
    · ext ⟨i,j⟩; fin_cases i <;> rfl
  map_add' x y := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext j <;> rfl
  map_smul' a x := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext j <;> rfl

/-- Splitting copy one from copies two and three is an orthogonal coordinate map. -/
def splitCubeConfigIsometry (m : ℕ) :
    CopiesConfig m 3 ≃ₗᵢ[ℝ] WithLp 2 (WaveConfig m × BosonConfig m) where
  toLinearEquiv := splitCubeConfig m
  norm_map' z := by
    have h : ‖splitCubeConfig m z‖ ^ 2 = ‖z‖ ^ 2 := by
      simp only [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq,
        Fintype.sum_prod_type, Fin.sum_univ_succ]
      rfl
    nlinarith [norm_nonneg (splitCubeConfig m z), norm_nonneg z]

/-- The three-copy position split preserves Lebesgue measure. -/
theorem cubePositions_measurePreserving (m : ℕ) :
    MeasurePreserving (fun z : CopiesConfig m 3 => (cubePosition 0 z, cubeTail z))
      volume (volume.prod volume) :=
  (WithLp.volume_preserving_ofLp (WaveConfig m) (BosonConfig m)).comp
    (splitCubeConfigIsometry m).measurePreserving

/-- Identify the split product configuration with three-copy wavefunctions. -/
def cubeProductEquiv (m : ℕ) :
    Lp ℂ 2 ((volume : Measure (WaveConfig m)).prod (volume : Measure (BosonConfig m)))
      ≃ₗᵢ[ℂ] CopiesWaveSpace m 3 := by
  let split := fun z : CopiesConfig m 3 => (cubePosition 0 z, cubeTail z)
  let join := fun xy : WaveConfig m × BosonConfig m =>
    (splitCubeConfigIsometry m).symm (WithLp.toLp 2 xy)
  have hjoin : MeasurePreserving join (volume.prod volume) volume :=
    (splitCubeConfigIsometry m).symm.measurePreserving.comp
      (WithLp.volume_preserving_toLp (WaveConfig m) (BosonConfig m))
  apply LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ split (cubePositions_measurePreserving m))
  intro f
  refine ⟨Lp.compMeasurePreserving join hjoin f, ?_⟩
  change Lp.compMeasurePreserving split _ (Lp.compMeasurePreserving join hjoin f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hid : join ∘ split = id := by
    funext z
    exact (splitCubeConfigIsometry m).symm_apply_apply z
  simpa only [hid] using Lp.compMeasurePreserving_id_apply f

/-- Identify the last two factors of the Hilbert cube with two-copy wavefunctions. -/
def cubeFactorsEquiv (m : ℕ) :
    HilbertCube (WaveSpace m) ≃ₗᵢ[ℂ] HilbertTensor (WaveSpace m) (SchrodingerSpace m) := by
  let e := TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (WaveSpace m))
    (waveTensorEquiv m)
  let L := e.toLinearIsometry.completion
  apply LinearIsometryEquiv.ofSurjective L
  intro v
  refine ⟨e.symm.toLinearIsometry.completion v, ?_⟩
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq (L.continuous.comp e.symm.toLinearIsometry.completion.continuous) continuous_id)
    fun w => ?_
  simp [L, LinearIsometry.completion_apply_coe]

private theorem cubeFactorsEquiv_tmul (m : ℕ) (f : WaveSpace m)
    (v : HilbertSquare (WaveSpace m)) :
    cubeFactorsEquiv m (hilbertTmul f v) = hilbertTmul f (waveTensorEquiv m v) :=
  (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (WaveSpace m))
    (waveTensorEquiv m)).toLinearIsometry.completion_apply_coe (f ⊗ₜ[ℂ] v)

/-- Canonical unitary from the completed Hilbert cube to three-copy wavefunctions. -/
def waveCubeEquiv (m : ℕ) : HilbertCube (WaveSpace m) ≃ₗᵢ[ℂ] CopiesWaveSpace m 3 :=
  (cubeFactorsEquiv m).trans
    ((productLpTensorEquiv (volume : Measure (WaveConfig m))
      (volume : Measure (BosonConfig m))).trans (cubeProductEquiv m))

/-- A tensor of one copy and an arbitrary last-two-copy vector is a product
of the corresponding physical wavefunctions. -/
theorem waveCubeEquiv_tmul_coeFn (m : ℕ) (f : WaveSpace m)
    (v : HilbertSquare (WaveSpace m)) :
    (waveCubeEquiv m (hilbertTmul f v) : CopiesConfig m 3 → ℂ) =ᵐ[volume]
      fun z => f (cubePosition 0 z) * waveTensorEquiv m v (cubeTail z) := by
  change cubeProductEquiv m
    (productLpTensorEquiv volume volume (cubeFactorsEquiv m (hilbertTmul f v))) =ᵐ[volume] _
  rw [cubeFactorsEquiv_tmul, productLpTensorEquiv_tmul]
  exact (Lp.coeFn_compMeasurePreserving (productLp f (waveTensorEquiv m v))
    (cubePositions_measurePreserving m)).trans
    ((cubePositions_measurePreserving m).quasiMeasurePreserving.ae_eq_comp
      (productLp_coeFn f (waveTensorEquiv m v)))

/-- An elementary three-copy tensor is the product of its three wavefunctions. -/
theorem waveCubeEquiv_triple_coeFn (m : ℕ) (f g h : WaveSpace m) :
    (waveCubeEquiv m (hilbertTmul f (hilbertTmul g h)) : CopiesConfig m 3 → ℂ) =ᵐ[volume]
      fun z => f (cubePosition 0 z) * (g (cubePosition 1 z) * h (cubePosition 2 z)) := by
  have htail : QuasiMeasurePreserving (cubeTail (m := m)) volume volume :=
    quasiMeasurePreserving_snd.comp (cubePositions_measurePreserving m).quasiMeasurePreserving
  filter_upwards [waveCubeEquiv_tmul_coeFn m f (hilbertTmul g h),
    htail.ae_eq_comp (waveTensor_tmul_coeFn m g h)] with z hz ht
  exact hz.trans (congrArg (fun w => f (cubePosition 0 z) * w) ht)

end
end GaussianTesting
