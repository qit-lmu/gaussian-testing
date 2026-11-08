module

public import GaussianTesting.Kac.SO3Topology
public import GaussianTesting.Kac.SO3Rotations
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Normalized surface measure for the spherical Kac walk

The sphere is the Euclidean unit sphere in ℝ³. Its measure is Mathlib's
surface measure obtained from Lebesgue measure by radial cones, normalized
to total mass one. The standard SO(3) action preserves this measure.
-/

namespace GaussianTesting.SO3

open MeasureTheory Matrix Set Metric
open scoped Pointwise ENNReal

noncomputable section

set_option maxHeartbeats 800000

/-- The real three-dimensional position space for the spherical Kac walk. -/
abbrev SphereAmbient := EuclideanSpace ℝ (Fin 3)

/-- The actual two-dimensional unit sphere in Euclidean three-space. -/
abbrev Sphere := Metric.sphere (0 : SphereAmbient) 1

/-- Unnormalized Euclidean surface measure, defined by radial cones. -/
def sphereSurfaceMeasure : Measure Sphere := (volume : Measure SphereAmbient).toSphere

instance sphereSurfaceMeasure_isFiniteMeasure : IsFiniteMeasure sphereSurfaceMeasure := by
  unfold sphereSurfaceMeasure
  infer_instance

instance sphereSurfaceMeasure_neZero : NeZero sphereSurfaceMeasure :=
  ⟨Measure.toSphere_ne_zero volume⟩

/-- Normalized surface measure on the unit sphere. -/
def sphereMeasure : Measure Sphere :=
  (sphereSurfaceMeasure Set.univ)⁻¹ • sphereSurfaceMeasure

instance sphereMeasure_isProbabilityMeasure : IsProbabilityMeasure sphereMeasure := by
  unfold sphereMeasure
  infer_instance

/-- The sphere has total normalized surface measure one. -/
@[simp] theorem sphereMeasure_univ : sphereMeasure Set.univ = 1 := measure_univ

private theorem norm_rotationLinear (g : Group) (x : SphereAmbient) :
    ‖Matrix.toEuclideanLin (g : Matrix (Fin 3) (Fin 3) ℝ) x‖ = ‖x‖ := by
  have hg : (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * g = 1 :=
    (Matrix.mem_orthogonalGroup_iff' _ _).mp g.property.1
  have h : (g.val *ᵥ (WithLp.ofLp x)) ⬝ᵥ (g.val *ᵥ (WithLp.ofLp x)) =
      (WithLp.ofLp x) ⬝ᵥ (WithLp.ofLp x) := by
    rw [← Matrix.dotProduct_transpose_mulVec g.val (WithLp.ofLp x)
      (g.val *ᵥ (WithLp.ofLp x)), Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
  have hs : ‖Matrix.toEuclideanLin g.val x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Matrix.mulVec, pow_two] using h
  nlinarith [norm_nonneg (Matrix.toEuclideanLin g.val x), norm_nonneg x]

/-- The ordinary matrix rotation on Euclidean three-space. -/
def rotationEquiv (g : Group) : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient :=
  LinearIsometryEquiv.ofLinearIsometry
    { Matrix.toEuclideanLin (g : Matrix (Fin 3) (Fin 3) ℝ) with
      norm_map' := by exact norm_rotationLinear g }
    (Matrix.toEuclideanLin (g⁻¹ : Group).val)
    (by
      ext x : 1
      change Matrix.toEuclideanLin g.val (Matrix.toEuclideanLin (g⁻¹ : Group).val x) = x
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
      change Matrix.toEuclideanLin (g * g⁻¹).val x = x
      simp [Matrix.toEuclideanLin])
    (by
      ext x : 1
      change Matrix.toEuclideanLin (g⁻¹ : Group).val (Matrix.toEuclideanLin g.val x) = x
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
      change Matrix.toEuclideanLin (g⁻¹ * g).val x = x
      simp [Matrix.toEuclideanLin])

@[simp] theorem rotationEquiv_apply (g : Group) (x : SphereAmbient) (i : Fin 3) :
    rotationEquiv g x i = ∑ j, g.val i j * x j := rfl

@[simp] theorem rotationEquiv_one (x : SphereAmbient) : rotationEquiv 1 x = x := by
  change Matrix.toEuclideanLin (1 : Group).val x = x
  simp [Matrix.toEuclideanLin]

@[simp] theorem rotationEquiv_mul (g h : Group) (x : SphereAmbient) :
    rotationEquiv (g * h) x = rotationEquiv g (rotationEquiv h x) := by
  change Matrix.toEuclideanLin (g.val * h.val) x =
    Matrix.toEuclideanLin g.val (Matrix.toEuclideanLin h.val x)
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]

/-- Rotation of a point of the unit sphere. -/
def sphereRotation (g : Group) (x : Sphere) : Sphere :=
  ⟨rotationEquiv g x, by simpa only [Metric.mem_sphere, dist_zero_right,
    (rotationEquiv g).norm_map] using x.property⟩

@[simp] theorem sphereRotation_coe (g : Group) (x : Sphere) :
    (sphereRotation g x : SphereAmbient) = rotationEquiv g x := rfl

@[simp] theorem sphereRotation_one (x : Sphere) : sphereRotation 1 x = x := by
  apply Subtype.ext
  exact rotationEquiv_one x

@[simp] theorem sphereRotation_mul (g h : Group) (x : Sphere) :
    sphereRotation (g * h) x = sphereRotation g (sphereRotation h x) := by
  apply Subtype.ext
  exact rotationEquiv_mul g h x

/-- The natural rotation action is jointly continuous on group and sphere. -/
theorem continuous_sphereRotation :
    Continuous (fun p : Group × Sphere => sphereRotation p.1 p.2) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  change Continuous (fun p : Group × Sphere => ∑ j, p.1.val i j * (p.2 : SphereAmbient) j)
  apply continuous_finsetSum
  intro j _
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i j).mul
    ((PiLp.continuous_apply 2 _ j).comp (continuous_subtype_val.comp continuous_snd))

/-- Rotations preserve the radial cones defining the surface measure. -/
private theorem sphereRotation_cone_preimage (g : Group) (s : Set Sphere) :
    Ioo (0 : ℝ) 1 • ((↑) '' (sphereRotation g ⁻¹' s)) =
      rotationEquiv g ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, rotationEquiv g z, ⟨sphereRotation g z, hz, rfl⟩,
      (map_smul (rotationEquiv g) r (z : SphereAmbient)).symm⟩
  · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, he⟩
    let w := sphereRotation g⁻¹ z
    have hw : sphereRotation g w = z := by
      dsimp only [w]
      rw [← sphereRotation_mul, mul_inv_cancel, sphereRotation_one]
    refine ⟨r, hr, (w : SphereAmbient), ⟨w, ?_, rfl⟩, ?_⟩
    · change sphereRotation g w ∈ s
      rw [hw]
      exact hz
    · apply (rotationEquiv g).injective
      rw [map_smul]
      change r • (sphereRotation g w : SphereAmbient) = rotationEquiv g x
      rw [hw]
      exact he

/-- Rotation invariance of the unnormalized Euclidean surface measure. -/
theorem sphereRotation_surfaceMeasurePreserving (g : Group) :
    MeasurePreserving (sphereRotation g) sphereSurfaceMeasure sphereSurfaceMeasure := by
  have hc : Continuous (sphereRotation g) :=
    continuous_sphereRotation.comp (continuous_const.prodMk continuous_id)
  refine ⟨hc.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hc.measurable hs]
  change (volume : Measure SphereAmbient).toSphere (sphereRotation g ⁻¹' s) =
    (volume : Measure SphereAmbient).toSphere s
  rw [Measure.toSphere_apply' _ (hc.measurable hs), Measure.toSphere_apply' _ hs,
    sphereRotation_cone_preimage]
  congr 1
  exact (rotationEquiv g).measurePreserving.measure_preimage_emb
    (rotationEquiv g).toHomeomorph.measurableEmbedding _

/-- The natural SO(3) action preserves normalized surface measure. -/
theorem sphereRotation_measurePreserving (g : Group) :
    MeasurePreserving (sphereRotation g) sphereMeasure sphereMeasure :=
  (sphereRotation_surfaceMeasurePreserving g).smul_measure _

end
end GaussianTesting.SO3
