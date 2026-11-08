module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

/-!
# Passing a rotation identity from a core to its graph closure

The integral form of `d(Uₜf)/dt = -i Uₜg` is continuous in both `f` and `g`.
It therefore holds on the closure of a finite-core graph. Strong continuity
implies that this closure is single valued; the same identity proves that
every vector in the closed generator's kernel is fixed by every rotation.
-/

namespace GaussianTesting.RotationGraphClosure

open MeasureTheory Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable (U : ℝ → E →ₗᵢ[ℂ] E) (hU : ∀ x, Continuous (fun t => U t x))

/-- The integrated orbit of the proposed generator value. -/
def integralMap (t : ℝ) : E →L[ℂ] E :=
  (show E →ₗ[ℂ] E from
    { toFun := fun y => ∫ s in (0 : ℝ)..t, (-Complex.I) • U s y
      map_add' := by
        intro y z
        simp only [map_add, smul_add]
        exact intervalIntegral.integral_add
          ((hU y).const_smul _ |>.intervalIntegrable _ _)
          ((hU z).const_smul _ |>.intervalIntegrable _ _)
      map_smul' := by
        intro c y
        simp only [map_smul, smul_comm (-Complex.I) c]
        exact intervalIntegral.integral_smul c _ }).mkContinuous |t| (by
    intro y
    change ‖∫ s in (0 : ℝ)..t, (-Complex.I) • U s y‖ ≤ |t| * ‖y‖
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (C := ‖y‖)
      (f := fun s => (-Complex.I) • U s y) (by
        intro s _
        simp only [norm_smul, norm_neg, Complex.norm_I, one_mul,
          LinearIsometry.norm_map, le_refl])
    simpa only [sub_zero, mul_comm] using hb)

omit [CompleteSpace E] in
@[simp] theorem integralMap_apply (t : ℝ) (y : E) :
    integralMap U hU t y = ∫ s in (0 : ℝ)..t, (-Complex.I) • U s y := rfl

variable (hzero : ∀ x, U 0 x = x) (S : Submodule ℂ (E × E))
variable (hderiv : ∀ z ∈ S, ∀ t,
  HasDerivAt (fun s => U s z.1) ((-Complex.I) • U t z.2) t)

include hU hzero hderiv

/-- The differential equation on the initial graph integrates to an identity
on its entire topological closure. -/
theorem integrated_identity {z : E × E} (hz : z ∈ S.topologicalClosure) (t : ℝ) :
    U t z.1 - z.1 = integralMap U hU t z.2 := by
  have hc : IsClosed {z : E × E | U t z.1 - z.1 = integralMap U hU t z.2} :=
    isClosed_eq (((U t).continuous.comp continuous_fst).sub continuous_fst)
      ((integralMap U hU t).continuous.comp continuous_snd)
  apply closure_minimal (s := (S : Set (E × E))) ?_ hc hz
  intro z hz
  change U t z.1 - z.1 = integralMap U hU t z.2
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (fun s _ => hderiv z hz s)
    ((hU z.2).const_smul (-Complex.I) |>.intervalIntegrable _ _)
  simpa only [hzero, integralMap_apply] using hi.symm

/-- Strong continuity excludes a nonzero value above the zero input in the
closed graph. In particular, no closability assumption is required. -/
theorem singleValued (z : E × E) (hz : z ∈ S.topologicalClosure)
    (hf : z.1 = 0) : z.2 = 0 := by
  have he : (fun t => ∫ s in (0 : ℝ)..t, (-Complex.I) • U s z.2) =
      fun _ => (0 : E) := by
    funext t
    have h := integrated_identity U hU hzero S hderiv hz t
    simpa only [hf, map_zero, sub_zero, integralMap_apply] using h.symm
  have hc := (hU z.2).const_smul (-Complex.I)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (a := (0 : ℝ)) (b := (0 : ℝ)) (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, (-Complex.I) • U s z.2)
    ((-Complex.I) • U 0 z.2) 0 at hd
  rw [he, hzero] at hd
  have hv : (-Complex.I) • z.2 = 0 := hd.unique (hasDerivAt_const 0 (0 : E))
  exact (smul_eq_zero.mp hv).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

/-- The actual graph closure, now known to be the graph of an operator. -/
def closedGenerator : E →ₗ.[ℂ] E := S.topologicalClosure.toLinearPMap

theorem closedGenerator_graph :
    (closedGenerator S).graph = S.topologicalClosure :=
  Submodule.toLinearPMap_graph_eq _ (singleValued U hU hzero S hderiv)

theorem closedGenerator_isClosed : (closedGenerator S).IsClosed := by
  rw [LinearPMap.IsClosed, closedGenerator_graph U hU hzero S hderiv]
  exact S.isClosed_topologicalClosure

/-- A vector in the graph-closed generator's kernel is fixed by every rotation. -/
theorem fixed_of_mem_ker {f : E} (hf : f ∈ (closedGenerator S).ker) (t : ℝ) :
    U t f = f := by
  obtain ⟨x, hx, hy⟩ := (closedGenerator S).mem_ker_iff.mp hf
  have hg : (f, 0) ∈ S.topologicalClosure := by
    rw [← closedGenerator_graph U hU hzero S hderiv]
    exact (closedGenerator S).mem_graph_iff.mpr ⟨x, hx.symm, hy⟩
  have hi := integrated_identity U hU hzero S hderiv hg t
  simpa only [map_zero, sub_eq_zero] using hi

end
end GaussianTesting.RotationGraphClosure
