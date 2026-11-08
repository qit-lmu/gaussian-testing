module

/-
The finite-dimensional angular-momentum inequality used for Theorem 4.1 (`thm:kac-walk`).

`kacGapOn_of_split` reduces the inequality to invariant orthogonal summands.
On an irreducible triple, `kacGapOn_of_irreducible` constructs a weight basis
for `Jz`, computes the kernels of `Jx` and `Jy`, and chooses their phases
to obtain the manuscript's common overlap `a_j`. `Kac/SpinOverlap.lean` gives
its alternating binomial-square formula, and `Kac/SpinGram.lean` computes
the exact two nonzero eigenvalues and their maximum `λ_j`. Strong induction
on the dimension then gives `kacGapOn_all`.
-/
public import GaussianTesting.Kac.Defs
public import GaussianTesting.Kac.Binomial
public import GaussianTesting.Kac.SpinGram
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

namespace GaussianTesting

open scoped InnerProductSpace
open Finset

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

namespace AngularMomentum

/-- A subspace invariant under the triple. -/
def Invariant (J : AngularMomentum V) (U : Submodule ℂ V) : Prop :=
  (∀ u ∈ U, J.Jx u ∈ U) ∧ (∀ u ∈ U, J.Jy u ∈ U) ∧ (∀ u ∈ U, J.Jz u ∈ U)

/-- An irreducible triple. -/
def Irreducible (J : AngularMomentum V) : Prop :=
  ∀ U : Submodule ℂ V, J.Invariant U → U = ⊥ ∨ U = ⊤

/-- The spectral-gap conclusion for a given triple (matching `kacT_gap`). -/
def KacGapOn (J : AngularMomentum V) : Prop :=
  ∀ f : V, 0 ≤ (⟪f, ((kacT J - LinearMap.id) ∘ₗ
      (kacT J - (((7 / 12 : ℝ) : ℂ) • LinearMap.id))) f⟫_ℂ).re

omit [FiniteDimensional ℂ V] in
private lemma symmetric_invariant_orthogonal (A : V →ₗ[ℂ] V)
    (hA : A.IsSymmetric) {U : Submodule ℂ V}
    (hU : ∀ u ∈ U, A u ∈ U) : ∀ w ∈ Uᗮ, A w ∈ Uᗮ := by
  intro w hw
  apply (U.mem_orthogonal _).2
  intro u hu
  rw [← hA u w]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hw

omit [FiniteDimensional ℂ V] in
private lemma symmetric_restrict (A : V →ₗ[ℂ] V) (hA : A.IsSymmetric)
    {U : Submodule ℂ V} (hU : ∀ u ∈ U, A u ∈ U) :
    (A.restrict hU).IsSymmetric := by
  intro u v
  exact hA (u : V) (v : V)

omit [FiniteDimensional ℂ V] in
private lemma comm_restrict (A B C : V →ₗ[ℂ] V)
    {U : Submodule ℂ V} (hA : ∀ u ∈ U, A u ∈ U)
    (hB : ∀ u ∈ U, B u ∈ U) (hC : ∀ u ∈ U, C u ∈ U)
    (h : ⁅A, B⁆ = Complex.I • C) :
    ⁅A.restrict hA, B.restrict hB⁆ = Complex.I • C.restrict hC := by
  ext u
  have hh := LinearMap.congr_fun h (u : V)
  simpa [Ring.lie_def, Module.End.mul_apply] using hh

omit [FiniteDimensional ℂ V] in
/-- Orthogonal complements of invariant subspaces are invariant (the generators are
Hermitian). -/
lemma invariant_orthogonal [FiniteDimensional ℂ V] (J : AngularMomentum V) {U : Submodule ℂ V}
    (hU : J.Invariant U) : J.Invariant Uᗮ := by
  exact ⟨symmetric_invariant_orthogonal J.Jx J.hJx hU.1,
    symmetric_invariant_orthogonal J.Jy J.hJy hU.2.1,
    symmetric_invariant_orthogonal J.Jz J.hJz hU.2.2⟩

/-- Restriction of the triple to an invariant subspace. -/
def restrictJ (J : AngularMomentum V) (U : Submodule ℂ V) (hU : J.Invariant U) :
    AngularMomentum U where
  Jx := J.Jx.restrict hU.1
  Jy := J.Jy.restrict hU.2.1
  Jz := J.Jz.restrict hU.2.2
  hJx := by
    exact symmetric_restrict J.Jx J.hJx hU.1
  hJy := by
    exact symmetric_restrict J.Jy J.hJy hU.2.1
  hJz := by
    exact symmetric_restrict J.Jz J.hJz hU.2.2
  comm_xy := by
    exact comm_restrict J.Jx J.Jy J.Jz hU.1 hU.2.1 hU.2.2 J.comm_xy
  comm_yz := by
    exact comm_restrict J.Jy J.Jz J.Jx hU.2.1 hU.2.2 hU.1 J.comm_yz
  comm_zx := by
    exact comm_restrict J.Jz J.Jx J.Jy hU.2.2 hU.1 hU.2.1 J.comm_zx

private lemma projection_ker_restrict (A : V →ₗ[ℂ] V) (hA : A.IsSymmetric)
    {U : Submodule ℂ V} (hU : ∀ u ∈ U, A u ∈ U) (u : U) :
    (LinearMap.ker A).starProjection (u : V) =
      ((LinearMap.ker (A.restrict hU)).starProjection u : V) := by
  let K := LinearMap.ker (A.restrict hU)
  have proj_comm (k : V) : U.starProjection (A k) = A (U.starProjection k) := by
    apply U.eq_starProjection_of_mem_orthogonal (hU _ (U.starProjection_apply_mem k))
    rw [← map_sub]
    exact symmetric_invariant_orthogonal A hA hU _ (U.sub_starProjection_mem_orthogonal k)
  apply (LinearMap.ker A).eq_starProjection_of_mem_of_inner_eq_zero
  · have hp := K.starProjection_apply_mem u
    have hh := congrArg (fun x : U => (x : V)) (LinearMap.mem_ker.mp hp)
    exact LinearMap.mem_ker.mpr hh
  · intro k hk
    let ku : U := ⟨U.starProjection k, U.starProjection_apply_mem k⟩
    have hku : ku ∈ K := by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change A (U.starProjection k) = 0
      rw [← proj_comm, LinearMap.mem_ker.mp hk, map_zero]
    have hfirst : ⟪(u : V) - (K.starProjection u : V), (ku : V)⟫_ℂ = 0 :=
      K.starProjection_inner_eq_zero u ku hku
    have hsecond : ⟪(u : V) - (K.starProjection u : V), k - (ku : V)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (U.sub_mem u.property (K.starProjection u).property)
        (U.sub_starProjection_mem_orthogonal k)
    have heq : k = (ku : V) + (k - (ku : V)) := by abel
    rw [heq, inner_add_right, hfirst, hsecond, add_zero]

/-- For `u ∈ U` invariant, the ambient kernel projection agrees with the restricted
one: `ker A = (ker A ∩ U) ⊕ (ker A ∩ Uᗮ)` for Hermitian `A` preserving `U` and `Uᗮ`,
and the orthogonal part of `u` relative to `ker (A|U)` is orthogonal to all of
`ker A`. -/
lemma starProjection_ker_apply_of_invariant (J : AngularMomentum V)
    {U : Submodule ℂ V} (hU : J.Invariant U) (u : U) :
    (LinearMap.ker J.Jx).starProjection (u : V)
      = ((LinearMap.ker (J.restrictJ U hU).Jx).starProjection u : V) := by
  exact projection_ker_restrict J.Jx J.hJx hU.1 u

/-- Same for `Jy` (by the analogous argument). -/
lemma starProjection_ker_apply_of_invariant_y (J : AngularMomentum V)
    {U : Submodule ℂ V} (hU : J.Invariant U) (u : U) :
    (LinearMap.ker J.Jy).starProjection (u : V)
      = ((LinearMap.ker (J.restrictJ U hU).Jy).starProjection u : V) := by
  exact projection_ker_restrict J.Jy J.hJy hU.2.1 u

/-- Same for `Jz`. -/
lemma starProjection_ker_apply_of_invariant_z (J : AngularMomentum V)
    {U : Submodule ℂ V} (hU : J.Invariant U) (u : U) :
    (LinearMap.ker J.Jz).starProjection (u : V)
      = ((LinearMap.ker (J.restrictJ U hU).Jz).starProjection u : V) := by
  exact projection_ker_restrict J.Jz J.hJz hU.2.2 u

/-- The Kac operator restricts along invariant subspaces. -/
lemma kacT_apply_of_invariant (J : AngularMomentum V) {U : Submodule ℂ V}
    (hU : J.Invariant U) (u : U) :
    kacT J (u : V) = (kacT (J.restrictJ U hU) u : V) := by
  simp only [kacT, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    add_apply, Submodule.coe_smul, Submodule.coe_add]
  rw [J.starProjection_ker_apply_of_invariant hU u,
    J.starProjection_ker_apply_of_invariant_y hU u,
    J.starProjection_ker_apply_of_invariant_z hU u]

/-- The gap predicate ascends along invariant orthogonal splittings. -/
lemma kacGapOn_of_split (J : AngularMomentum V) {U : Submodule ℂ V}
    (hU : J.Invariant U)
    (h1 : KacGapOn (J.restrictJ U hU))
    (h2 : KacGapOn (J.restrictJ Uᗮ (J.invariant_orthogonal hU))) :
    KacGapOn J := by
  let Q := (kacT J - LinearMap.id) ∘ₗ
    (kacT J - (((7 / 12 : ℝ) : ℂ) • LinearMap.id))
  have transport {S : Submodule ℂ V} (hS : J.Invariant S) (x : S) :
      Q (x : V) =
        ((((kacT (J.restrictJ S hS) - LinearMap.id) ∘ₗ
          (kacT (J.restrictJ S hS) - (((7 / 12 : ℝ) : ℂ) • LinearMap.id))) x : S) : V) := by
    let y : S := (kacT (J.restrictJ S hS) -
      (((7 / 12 : ℝ) : ℂ) • LinearMap.id) : S →ₗ[ℂ] S) x
    have hy : (kacT J - (((7 / 12 : ℝ) : ℂ) • LinearMap.id) : V →ₗ[ℂ] V) (x : V) = (y : V) := by
      simp [y, J.kacT_apply_of_invariant hS x]
    change (kacT J - LinearMap.id : V →ₗ[ℂ] V) _ = _
    rw [hy]
    change kacT J (y : V) - (y : V) =
      ((kacT (J.restrictJ S hS) y - y : S) : V)
    rw [J.kacT_apply_of_invariant hS y]
    rfl
  intro f
  let u : U := ⟨U.starProjection f, U.starProjection_apply_mem f⟩
  let w : Uᗮ := ⟨f - U.starProjection f, U.sub_starProjection_mem_orthogonal f⟩
  have hf : f = (u : V) + (w : V) := by dsimp [u, w]; abel
  have hQu : Q (u : V) ∈ U := by
    rw [transport hU u]
    exact Subtype.coe_prop _
  have hQw : Q (w : V) ∈ Uᗮ := by
    rw [transport (J.invariant_orthogonal hU) w]
    exact Subtype.coe_prop _
  have hu := h1 u
  have hw := h2 w
  change 0 ≤ (⟪f, Q f⟫_ℂ).re
  rw [hf, map_add, inner_add_left, inner_add_right, inner_add_right,
    Submodule.inner_right_of_mem_orthogonal u.property hQw,
    Submodule.inner_left_of_mem_orthogonal hQu w.property,
    add_zero, zero_add, Complex.add_re,
    transport hU u, transport (J.invariant_orthogonal hU) w]
  exact add_nonneg hu hw

private def raising (J : AngularMomentum V) : Module.End ℂ V :=
  J.Jx + Complex.I • J.Jy

private def lowering (J : AngularMomentum V) : Module.End ℂ V :=
  J.Jx - Complex.I • J.Jy

omit [FiniteDimensional ℂ V] in
private lemma raising_adjoint [FiniteDimensional ℂ V] (J : AngularMomentum V) (u v : V) :
    ⟪raising J u, v⟫_ℂ = ⟪u, lowering J v⟫_ℂ := by
  simp [raising, lowering, inner_add_left, inner_add_right, inner_neg_right, inner_smul_left,
    inner_smul_right, J.hJx u v, J.hJy u v, sub_eq_add_neg]

omit [FiniteDimensional ℂ V] in
private lemma raising_comm [FiniteDimensional ℂ V] (J : AngularMomentum V) :
    J.Jz ∘ₗ raising J = raising J ∘ₗ J.Jz + raising J := by
  have hx := J.comm_zx
  have hy := J.comm_yz
  simp only [Ring.lie_def] at hx hy
  unfold raising
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul,
    LinearMap.smul_comp]
  have hy' : J.Jz * J.Jy = J.Jy * J.Jz - Complex.I • J.Jx := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hy).symm
  have hx' : J.Jz * J.Jx = J.Jx * J.Jz + Complex.I • J.Jy := by
    simpa [add_comm] using sub_eq_iff_eq_add.mp hx
  change J.Jz * J.Jx + Complex.I • (J.Jz * J.Jy) = _
  rw [hx', hy']
  simp [smul_sub, smul_smul, Complex.I_mul_I]
  change J.Jx * J.Jz + Complex.I • J.Jy +
    (Complex.I • (J.Jy * J.Jz) + J.Jx) = _
  change _ = J.Jx * J.Jz + Complex.I • (J.Jy * J.Jz) +
    (J.Jx + Complex.I • J.Jy)
  abel

omit [FiniteDimensional ℂ V] in
private lemma lowering_comm [FiniteDimensional ℂ V] (J : AngularMomentum V) :
    J.Jz ∘ₗ lowering J = lowering J ∘ₗ J.Jz - lowering J := by
  have hx := J.comm_zx
  have hy := J.comm_yz
  simp only [Ring.lie_def] at hx hy
  unfold lowering
  simp only [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_smul,
    LinearMap.smul_comp]
  have hy' : J.Jz * J.Jy = J.Jy * J.Jz - Complex.I • J.Jx := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hy).symm
  have hx' : J.Jz * J.Jx = J.Jx * J.Jz + Complex.I • J.Jy := by
    simpa [add_comm] using sub_eq_iff_eq_add.mp hx
  change J.Jz * J.Jx - Complex.I • (J.Jz * J.Jy) = _
  rw [hx', hy']
  simp [smul_sub, smul_smul, Complex.I_mul_I]
  change _ = (J.Jx * J.Jz - Complex.I • (J.Jy * J.Jz)) -
    (J.Jx - Complex.I • J.Jy)
  abel

omit [FiniteDimensional ℂ V] in
private lemma ladder_comm [FiniteDimensional ℂ V] (J : AngularMomentum V) :
    raising J ∘ₗ lowering J = lowering J ∘ₗ raising J + (2 : ℂ) • J.Jz := by
  have h := J.comm_xy
  simp only [Ring.lie_def] at h
  have h' : J.Jx * J.Jy = J.Jy * J.Jx + Complex.I • J.Jz := by
    simpa [add_comm] using sub_eq_iff_eq_add.mp h
  unfold raising lowering
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_sub,
    LinearMap.sub_comp, LinearMap.comp_smul, LinearMap.smul_comp]
  change J.Jx * J.Jx + Complex.I • (J.Jy * J.Jx) -
    Complex.I • (J.Jx * J.Jy + Complex.I • (J.Jy * J.Jy)) =
    J.Jx * J.Jx - Complex.I • (J.Jy * J.Jx) +
    Complex.I • (J.Jx * J.Jy - Complex.I • (J.Jy * J.Jy)) + 2 • J.Jz
  rw [h']
  simp only [smul_sub, smul_add, smul_smul, Complex.I_mul_I]
  module

private lemma highest_weight (J : AngularMomentum V) {n : ℕ}
    (hn : Module.finrank ℂ V = n + 1) :
    ∃ (μ : ℝ) (v : V), ‖v‖ = 1 ∧
      J.Jz v = (μ : ℂ) • v ∧ raising J v = 0 := by
  let μ := J.hJz.eigenvalues hn 0
  let v := J.hJz.eigenvectorBasis hn 0
  refine ⟨μ, v, (J.hJz.eigenvectorBasis hn).orthonormal.norm_eq_one 0,
    J.hJz.apply_eigenvectorBasis hn 0, ?_⟩
  by_contra hv
  have he : J.Jz (raising J v) = ((μ + 1 : ℝ) : ℂ) • raising J v := by
    have hc := LinearMap.congr_fun (raising_comm J) v
    change J.Jz (raising J v) = raising J (J.Jz v) + raising J v at hc
    rw [hc, J.hJz.apply_eigenvectorBasis hn 0, map_smul]
    simp [μ, v, add_smul]
  have hev : Module.End.HasEigenvalue J.Jz ((μ + 1 : ℝ) : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩
  obtain ⟨i, hi⟩ := J.hJz.exists_eigenvalues_eq hn hev
  have hi' : J.hJz.eigenvalues hn i = μ + 1 := by
    exact Complex.ofReal_injective hi
  have hle := J.hJz.eigenvalues_antitone hn (Fin.zero_le i)
  rw [hi'] at hle
  change μ + 1 ≤ μ at hle
  linarith

private def weightString (J : AngularMomentum V) (v : V) (k : ℕ) : V :=
  (lowering J ^ k) v

omit [FiniteDimensional ℂ V] in
private lemma weightString_zero [FiniteDimensional ℂ V] (J : AngularMomentum V) (v : V) :
    weightString J v 0 = v := rfl

omit [FiniteDimensional ℂ V] in
private lemma weightString_succ [FiniteDimensional ℂ V] (J : AngularMomentum V) (v : V) (k : ℕ) :
    weightString J v (k + 1) = lowering J (weightString J v k) := by
  simp [weightString, pow_succ', Module.End.mul_apply]

private lemma weightString_weight (J : AngularMomentum V) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) (k : ℕ) :
    J.Jz (weightString J v k) = ((μ - k : ℝ) : ℂ) • weightString J v k := by
  induction k with
  | zero => simpa [weightString_zero] using hv
  | succ k ih =>
    have hc := LinearMap.congr_fun (lowering_comm J) (weightString J v k)
    change J.Jz (lowering J (weightString J v k)) =
      lowering J (J.Jz (weightString J v k)) - lowering J (weightString J v k) at hc
    rw [weightString_succ, hc, ih, map_smul]
    simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one]
    module

private lemma weightString_raising (J : AngularMomentum V) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) (hp : raising J v = 0) (k : ℕ) :
    raising J (weightString J v (k + 1)) =
      (((k + 1) * (2 * μ - k) : ℝ) : ℂ) • weightString J v k := by
  induction k with
  | zero =>
    have hc := LinearMap.congr_fun (ladder_comm J) v
    change raising J (lowering J v) = lowering J (raising J v) + (2 : ℂ) • J.Jz v at hc
    rw [hp, map_zero, hv, zero_add, smul_smul] at hc
    convert hc using 1 <;> simp [weightString_succ, weightString_zero]

  | succ k ih =>
    have hc := LinearMap.congr_fun (ladder_comm J) (weightString J v (k + 1))
    change raising J (lowering J (weightString J v (k + 1))) =
      lowering J (raising J (weightString J v (k + 1))) +
        (2 : ℂ) • J.Jz (weightString J v (k + 1)) at hc
    rw [weightString_succ, hc, ih, map_smul, weightString_weight J hv,
      ← weightString_succ]
    simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Nat.cast_add, Nat.cast_one]
    module

private lemma weightString_norm (J : AngularMomentum V) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) (hp : raising J v = 0) (k : ℕ) :
    ‖weightString J v (k + 1)‖ ^ 2 =
      ((k + 1) * (2 * μ - k)) * ‖weightString J v k‖ ^ 2 := by
  have h := raising_adjoint J (weightString J v (k + 1)) (weightString J v k)
  rw [weightString_raising J hv hp, ← weightString_succ, inner_smul_left] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  change (starRingEnd ℂ) (((k + 1) * (2 * μ - k) : ℝ) : ℂ) *
    (‖weightString J v k‖ : ℂ) ^ 2 = (‖weightString J v (k + 1)‖ : ℂ) ^ 2 at h
  simp only [Complex.conj_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul] at h
  exact (Complex.ofReal_injective h).symm

private lemma weightString_orthogonal (J : AngularMomentum V) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) {k l : ℕ} (hkl : k ≠ l) :
    ⟪weightString J v k, weightString J v l⟫_ℂ = 0 := by
  have h := J.hJz (weightString J v k) (weightString J v l)
  rw [weightString_weight J hv, weightString_weight J hv,
    inner_smul_left, inner_smul_right] at h
  simp only [Complex.conj_ofReal] at h
  have hne : ((μ - k : ℝ) : ℂ) ≠ ((μ - l : ℝ) : ℂ) := by
    intro he
    have he' : (k : ℝ) = l := by
      have := Complex.ofReal_injective he
      linarith
    exact hkl (Nat.cast_injective he')
  exact (mul_eq_mul_right_iff.mp h).resolve_left hne

private lemma weightString_eventually_zero (J : AngularMomentum V) {n : ℕ}
    (hn : Module.finrank ℂ V = n + 1) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) : ∃ k, weightString J v k = 0 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (μ - J.hJz.eigenvalues hn (Fin.last n))
  refine ⟨k, ?_⟩
  by_contra hne
  have hev : Module.End.HasEigenvalue J.Jz ((μ - k : ℝ) : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (weightString_weight J hv k), hne⟩
  obtain ⟨i, hi⟩ := J.hJz.exists_eigenvalues_eq hn hev
  have hi' : J.hJz.eigenvalues hn i = μ - k := Complex.ofReal_injective hi
  have hle := J.hJz.eigenvalues_antitone hn (Fin.le_last i)
  rw [hi'] at hle
  linarith

private lemma weightString_zero_of_le (J : AngularMomentum V) {v : V} {k l : ℕ}
    (hk : weightString J v k = 0) (hkl : k ≤ l) : weightString J v l = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction d with
  | zero => simpa using hk
  | succ d ih => rw [← Nat.add_assoc, weightString_succ, ih, map_zero]

private lemma weightString_top (J : AngularMomentum V) {n : ℕ}
    (hn : Module.finrank ℂ V = n + 1) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) (hp : raising J v = 0) (hne : v ≠ 0) :
    ∃ m : ℕ, μ = (m : ℝ) / 2 ∧
      (∀ k ≤ m, weightString J v k ≠ 0) ∧ weightString J v (m + 1) = 0 := by
  classical
  have hex := weightString_eventually_zero J hn hv
  let r := Nat.find hex
  have hr : weightString J v r = 0 := Nat.find_spec hex
  have hrpos : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    rw [hr0, weightString_zero] at hr
    exact hne hr
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  have hmne : weightString J v m ≠ 0 := by
    apply Nat.find_min hex
    change m < r
    omega
  have hnorm := weightString_norm J hv hp m
  have hmzero : weightString J v (m + 1) = 0 := by simpa [hm] using hr
  rw [hmzero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
  have hnormpos : 0 < ‖weightString J v m‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hmne)
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  have hfac : 2 * μ - (m : ℝ) = 0 := by
    rcases (mul_eq_zero.mp hnorm.symm) with h | h
    · exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hmpos)
    · exact (ne_of_gt hnormpos h).elim
  have hmu : μ = (m : ℝ) / 2 := by linarith
  refine ⟨m, hmu, ?_, hmzero⟩
  intro k hk
  apply Nat.find_min hex
  change k < r
  omega

private lemma string_span_invariant (J : AngularMomentum V) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) (hp : raising J v = 0) :
    J.Invariant (Submodule.span ℂ (Set.range (weightString J v))) := by
  let W := Submodule.span ℂ (Set.range (weightString J v))
  have hw (k : ℕ) : weightString J v k ∈ W := Submodule.subset_span ⟨k, rfl⟩
  have hminus : ∀ u ∈ W, lowering J u ∈ W := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨k, rfl⟩ := hu
      rw [← weightString_succ]
      exact hw _
    | zero => simp
    | add u v _ _ ihu ihv => simpa using W.add_mem ihu ihv
    | smul a u _ ihu => simpa using W.smul_mem a ihu
  have hplus : ∀ u ∈ W, raising J u ∈ W := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨k, rfl⟩ := hu
      cases k with
      | zero => simp [weightString_zero, hp]
      | succ k => rw [weightString_raising J hv hp]; exact W.smul_mem _ (hw k)
    | zero => simp
    | add u v _ _ ihu ihv => simpa using W.add_mem ihu ihv
    | smul a u _ ihu => simpa using W.smul_mem a ihu
  have hz : ∀ u ∈ W, J.Jz u ∈ W := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨k, rfl⟩ := hu
      rw [weightString_weight J hv]
      exact W.smul_mem _ (hw k)
    | zero => simp
    | add u v _ _ ihu ihv => simpa using W.add_mem ihu ihv
    | smul a u _ ihu => simpa using W.smul_mem a ihu
  have hx (u : V) : J.Jx u = (2 : ℂ)⁻¹ • (raising J u + lowering J u) := by
    change J.Jx u = (2 : ℂ)⁻¹ •
      ((J.Jx u + Complex.I • J.Jy u) + (J.Jx u - Complex.I • J.Jy u))
    module
  have hy (u : V) : J.Jy u = (2 * Complex.I)⁻¹ • (raising J u - lowering J u) := by
    change J.Jy u = (2 * Complex.I)⁻¹ •
      ((J.Jx u + Complex.I • J.Jy u) - (J.Jx u - Complex.I • J.Jy u))
    have ha : (J.Jx u + Complex.I • J.Jy u) -
        (J.Jx u - Complex.I • J.Jy u) = (2 * Complex.I) • J.Jy u := by module
    rw [ha, smul_smul, inv_mul_cancel₀ (by simp), one_smul]
  exact ⟨fun u hu => hx u ▸ W.smul_mem _ (W.add_mem (hplus u hu) (hminus u hu)),
    fun u hu => hy u ▸ W.smul_mem _ (W.sub_mem (hplus u hu) (hminus u hu)), hz⟩

private lemma string_span_top (J : AngularMomentum V) (hJ : J.Irreducible)
    {μ : ℝ} {v : V} (hv : J.Jz v = (μ : ℂ) • v)
    (hp : raising J v = 0) (hne : v ≠ 0) :
    Submodule.span ℂ (Set.range (weightString J v)) = ⊤ := by
  rcases hJ _ (string_span_invariant J hv hp) with h | h
  · have hvspan : v ∈ Submodule.span ℂ (Set.range (weightString J v)) :=
      Submodule.subset_span (⟨0, weightString_zero J v⟩ :
      v ∈ Set.range (weightString J v))
    rw [h, Submodule.mem_bot] at hvspan
    exact (hne hvspan).elim
  · exact h

private def normalizedString (J : AngularMomentum V) (v : V) (m : ℕ)
    (k : Fin (m + 1)) : V :=
  (‖weightString J v k‖⁻¹ : ℂ) • weightString J v k

private lemma normalizedString_orthonormal (J : AngularMomentum V) {μ : ℝ} {v : V}
    (hv : J.Jz v = (μ : ℂ) • v) {m : ℕ}
    (hne : ∀ k ≤ m, weightString J v k ≠ 0) :
    Orthonormal ℂ (normalizedString J v m) := by
  refine ⟨?_, ?_⟩
  · intro k
    simpa [normalizedString] using
      norm_smul_inv_norm (𝕜 := ℂ) (hne k (by omega))
  · intro k l hkl
    have hval : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
    simp [normalizedString, inner_smul_left, inner_smul_right,
      weightString_orthogonal J hv hval]

private lemma normalizedString_span (J : AngularMomentum V) {v : V} {m : ℕ}
    (hne : ∀ k ≤ m, weightString J v k ≠ 0)
    (hzero : weightString J v (m + 1) = 0) :
    Submodule.span ℂ (Set.range (normalizedString J v m)) =
      Submodule.span ℂ (Set.range (weightString J v)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    by_cases hk : k ≤ m
    · have hmem : normalizedString J v m ⟨k, by omega⟩ ∈
          Submodule.span ℂ (Set.range (normalizedString J v m)) :=
        Submodule.subset_span (⟨⟨k, by omega⟩, rfl⟩ :
        normalizedString J v m ⟨k, by omega⟩ ∈ Set.range (normalizedString J v m))
      have heq : weightString J v k = (‖weightString J v k‖ : ℂ) •
          normalizedString J v m ⟨k, by omega⟩ := by
        simp [normalizedString, smul_smul, hne k hk]
      rw [heq]
      exact Submodule.smul_mem _ _ hmem
    · rw [weightString_zero_of_le J hzero (by omega)]
      exact Submodule.zero_mem _

private lemma irreducible_string_basis (J : AngularMomentum V) (hJ : J.Irreducible)
    {n : ℕ} (hn : Module.finrank ℂ V = n + 1) :
    ∃ v : V, ‖v‖ = 1 ∧ J.Jz v = (((n : ℝ) / 2 : ℝ) : ℂ) • v ∧
      raising J v = 0 ∧
      (∀ k ≤ n, weightString J v k ≠ 0) ∧ weightString J v (n + 1) = 0 ∧
      Submodule.span ℂ (Set.range (normalizedString J v n)) = ⊤ := by
  obtain ⟨μ, v, hnorm, hv, hp⟩ := highest_weight J hn
  have hne : v ≠ 0 := by intro h; simp [h] at hnorm
  obtain ⟨m, hmu, hmne, hmzero⟩ := weightString_top J hn hv hp hne
  have hspan : Submodule.span ℂ (Set.range (normalizedString J v m)) = ⊤ := by
    rw [normalizedString_span J hmne hmzero]
    exact string_span_top J hJ hv hp hne
  have hdim := finrank_span_eq_card (normalizedString_orthonormal J hv hmne).linearIndependent
  rw [hspan, finrank_top, hn, Fintype.card_fin] at hdim
  have hmn : m = n := by omega
  subst m
  exact ⟨v, hnorm, hmu ▸ hv, hp, hmne, hmzero, hspan⟩

private lemma normalizedString_weight (J : AngularMomentum V) {n : ℕ} {v : V}
    (hv : J.Jz v = (((n : ℝ) / 2 : ℝ) : ℂ) • v) (k : Fin (n + 1)) :
    J.Jz (normalizedString J v n k) =
      (((n : ℝ) / 2 - k : ℝ) : ℂ) • normalizedString J v n k := by
  simp only [normalizedString, map_smul, weightString_weight J hv]
  rw [smul_comm]

private lemma irreducible_weight_basis (J : AngularMomentum V) (hJ : J.Irreducible)
    {n : ℕ} (hn : Module.finrank ℂ V = n + 1) :
    ∃ b : OrthonormalBasis (Fin (n + 1)) ℂ V,
      ∀ k, J.Jz (b k) = (((n : ℝ) / 2 - k : ℝ) : ℂ) • b k := by
  obtain ⟨v, _, hv, _, hne, _, hspan⟩ := irreducible_string_basis J hJ hn
  let b := OrthonormalBasis.mk (normalizedString_orthonormal J hv hne) hspan.ge
  refine ⟨b, ?_⟩
  intro k
  simpa [b] using normalizedString_weight J hv k

private def cycle (J : AngularMomentum V) : AngularMomentum V where
  Jx := J.Jy
  Jy := J.Jz
  Jz := J.Jx
  hJx := J.hJy
  hJy := J.hJz
  hJz := J.hJx
  comm_xy := J.comm_yz
  comm_yz := J.comm_zx
  comm_zx := J.comm_xy

omit [FiniteDimensional ℂ V] in
private lemma cycle_irreducible [FiniteDimensional ℂ V] (J : AngularMomentum V) (hJ : J.Irreducible) :
    (cycle J).Irreducible := by
  intro U hU
  exact hJ U ⟨hU.2.2, hU.1, hU.2.1⟩

private lemma odd_weight_ker (J : AngularMomentum V) (hJ : J.Irreducible)
    {n : ℕ} (hn : Module.finrank ℂ V = n + 1) (hodd : Odd n) :
    LinearMap.ker J.Jz = ⊥ := by
  obtain ⟨b, hb⟩ := irreducible_weight_basis J hJ hn
  apply bot_unique
  intro f hf
  change f = 0
  apply b.repr.injective
  ext k
  rw [map_zero, PiLp.zero_apply, b.repr_apply_apply]
  have h := J.hJz (b k) f
  rw [hb, LinearMap.mem_ker.mp hf, inner_zero_right, inner_smul_left] at h
  have hweight : (((n : ℝ) / 2 - k : ℝ) : ℂ) ≠ 0 := by
    intro he
    have he' : (n : ℝ) / 2 - k = 0 := Complex.ofReal_eq_zero.mp he
    have he'' : n = 2 * (k : ℕ) := by exact_mod_cast (show (n : ℝ) = 2 * (k : ℝ) by linarith)
    obtain ⟨r, hr⟩ := hodd
    omega
  simp only [Complex.conj_ofReal] at h
  exact (mul_eq_zero.mp h).resolve_left hweight

omit [FiniteDimensional ℂ V] in
private lemma even_weight_ker [FiniteDimensional ℂ V] (J : AngularMomentum V) {j : ℕ}
    (b : OrthonormalBasis (Fin (2 * j + 1)) ℂ V)
    (hb : ∀ k, J.Jz (b k) = (((j : ℝ) - k : ℝ) : ℂ) • b k) :
    LinearMap.ker J.Jz = ℂ ∙ b ⟨j, by omega⟩ := by
  classical
  let i : Fin (2 * j + 1) := ⟨j, by omega⟩
  apply le_antisymm
  · intro f hf
    have hcoeff (k : Fin (2 * j + 1)) (hk : k ≠ i) : ⟪b k, f⟫_ℂ = 0 := by
      have h := J.hJz (b k) f
      rw [hb, LinearMap.mem_ker.mp hf, inner_zero_right, inner_smul_left] at h
      simp only [Complex.conj_ofReal] at h
      apply (mul_eq_zero.mp h).resolve_left
      intro he
      have he' : (j : ℝ) = k := sub_eq_zero.mp (Complex.ofReal_eq_zero.mp he)
      apply hk
      apply Fin.ext
      exact_mod_cast he'.symm
    have heq : f = ⟪b i, f⟫_ℂ • b i := by
      nth_rw 1 [← b.sum_repr f]
      rw [← b.repr_apply_apply]
      apply Finset.sum_eq_single i
      · intro k _ hk
        rw [b.repr_apply_apply, hcoeff k hk, zero_smul]
      · simp
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    rintro f (rfl : f = _)
    apply LinearMap.mem_ker.mpr
    simpa [i] using hb i

/-- Coefficients in the unnormalized even string. The denominator is the
raising coefficient at the next even position. -/
private def kernelCoefficient (j : ℕ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => kernelCoefficient j m / ((2 * m + 2) * (2 * j - 2 * m - 1) : ℝ)

private lemma kernelCoefficient_positive (j m : ℕ) (hm : m ≤ j) :
    0 < kernelCoefficient j m := by
  induction m with
  | zero => simp [kernelCoefficient]
  | succ m ih =>
    have hm' : m ≤ j := by omega
    have hden : (0 : ℝ) < (2 * m + 2) * (2 * j - 2 * m - 1) := by
      have hlt : (m : ℝ) + 1 ≤ j := by exact_mod_cast hm
      apply mul_pos <;> linarith
    exact div_pos (ih hm') hden

private lemma kernelCoefficient_step (j m : ℕ) (hm : m < j) :
    kernelCoefficient j (m + 1) * ((2 * m + 2) * (2 * j - 2 * m - 1) : ℝ) =
      kernelCoefficient j m := by
  have hden : ((2 * m + 2) * (2 * j - 2 * m - 1) : ℝ) ≠ 0 := by
    have hlt : (m : ℝ) + 1 ≤ j := by exact_mod_cast hm
    apply ne_of_gt
    apply mul_pos <;> linarith
  exact div_mul_cancel₀ _ hden

private def kernelString (J : AngularMomentum V) (v : V) (j : ℕ) (ε : ℝ) : V :=
  ∑ m ∈ Finset.range (j + 1),
    ((ε ^ m * kernelCoefficient j m : ℝ) : ℂ) • weightString J v (2 * m)

private lemma kernelString_lowering (J : AngularMomentum V) {v : V} {j : ℕ}
    (hzero : weightString J v (2 * j + 1) = 0) (ε : ℝ) :
    lowering J (kernelString J v j ε) =
      ∑ m ∈ Finset.range j,
        ((ε ^ m * kernelCoefficient j m : ℝ) : ℂ) • weightString J v (2 * m + 1) := by
  simp only [kernelString, map_sum, map_smul, ← weightString_succ]
  rw [Finset.sum_range_succ, hzero, smul_zero, add_zero]

private lemma kernelString_raising (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (ε : ℝ) :
    raising J (kernelString J v j ε) =
      ∑ m ∈ Finset.range j,
        ((ε ^ (m + 1) * kernelCoefficient j m : ℝ) : ℂ) •
          weightString J v (2 * m + 1) := by
  simp only [kernelString, map_sum, map_smul]
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero, weightString_zero, hp, smul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m < j := Finset.mem_range.mp hm
  have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [hidx, weightString_raising J (μ := j) hv hp, smul_smul]
  have hcoeff := kernelCoefficient_step j m hm'
  have hc : (2 * (m : ℂ) + 1 + 1) * (2 * j - (2 * m + 1)) =
      (2 * m + 2) * (2 * j - 2 * m - 1) := by ring
  push_cast
  rw [hc]
  have hcoeff' : (kernelCoefficient j (m + 1) : ℂ) *
      (((2 * m + 2) * (2 * j - 2 * m - 1) : ℝ) : ℂ) =
      (kernelCoefficient j m : ℂ) := by exact_mod_cast hcoeff
  push_cast at hcoeff'
  rw [mul_assoc, hcoeff']

private lemma kernelString_x_mem (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0)
    (hzero : weightString J v (2 * j + 1) = 0) :
    kernelString J v j (-1) ∈ LinearMap.ker J.Jx := by
  have hsum : raising J (kernelString J v j (-1)) +
      lowering J (kernelString J v j (-1)) = 0 := by
    rw [kernelString_raising J hv hp, kernelString_lowering J hzero, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro m _
    rw [← add_smul]
    simp [pow_succ]
  apply LinearMap.mem_ker.mpr
  change J.Jx (kernelString J v j (-1)) = 0
  change (J.Jx (kernelString J v j (-1)) + Complex.I • J.Jy (kernelString J v j (-1))) +
    (J.Jx (kernelString J v j (-1)) - Complex.I • J.Jy (kernelString J v j (-1))) = 0 at hsum
  have htwo : (2 : ℂ) • J.Jx (kernelString J v j (-1)) = 0 := by
    convert hsum using 1; module
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

private lemma kernelString_y_mem (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0)
    (hzero : weightString J v (2 * j + 1) = 0) :
    kernelString J v j 1 ∈ LinearMap.ker J.Jy := by
  have hdiff : raising J (kernelString J v j 1) -
      lowering J (kernelString J v j 1) = 0 := by
    rw [kernelString_raising J hv hp, kernelString_lowering J hzero]
    simp
  apply LinearMap.mem_ker.mpr
  change (J.Jx (kernelString J v j 1) + Complex.I • J.Jy (kernelString J v j 1)) -
    (J.Jx (kernelString J v j 1) - Complex.I • J.Jy (kernelString J v j 1)) = 0 at hdiff
  have htwo : (2 * Complex.I) • J.Jy (kernelString J v j 1) = 0 := by
    convert hdiff using 1; module
  exact (smul_eq_zero.mp htwo).resolve_left (by simp)

private lemma kernelString_nonzero (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hne : v ≠ 0) (ε : ℝ) :
    kernelString J v j ε ≠ 0 := by
  intro hzero
  have hinner := congrArg (fun u => ⟪v, u⟫_ℂ) hzero
  simp only [kernelString, inner_sum, inner_smul_right, inner_zero_right] at hinner
  have hsum : (∑ m ∈ Finset.range (j + 1),
      ((ε ^ m * kernelCoefficient j m : ℝ) : ℂ) * ⟪v, weightString J v (2 * m)⟫_ℂ) =
      ⟪v, v⟫_ℂ := by
    rw [Finset.sum_eq_single 0]
    · simp [kernelCoefficient, weightString_zero]
    · intro m _ hm
      have horth := weightString_orthogonal J (μ := j) hv
        (show (0 : ℕ) ≠ 2 * m by omega)
      simpa [weightString_zero] using congrArg
        (fun a : ℂ => ((ε ^ m * kernelCoefficient j m : ℝ) : ℂ) * a) horth
    · simp
  rw [hsum] at hinner
  exact hne (inner_self_eq_zero.mp hinner)

private lemma even_ker_finrank (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) :
    Module.finrank ℂ (LinearMap.ker J.Jz) = 1 := by
  obtain ⟨b, hb⟩ := irreducible_weight_basis J hJ hn
  have hb' (k : Fin (2 * j + 1)) :
      J.Jz (b k) = (((j : ℝ) - k : ℝ) : ℂ) • b k := by
    convert hb k using 1; push_cast; ring_nf
  rw [even_weight_ker J b hb']
  apply finrank_span_singleton
  exact b.orthonormal.ne_zero _

private def unitVector (u : V) : V := (‖u‖⁻¹ : ℂ) • u

omit [FiniteDimensional ℂ V] in
private lemma unitVector_norm [FiniteDimensional ℂ V] {u : V} (hu : u ≠ 0) : ‖unitVector u‖ = 1 := by
  exact norm_smul_inv_norm (𝕜 := ℂ) hu

omit [FiniteDimensional ℂ V] in
private lemma unitVector_span [FiniteDimensional ℂ V] {u : V} (hu : u ≠ 0) : ℂ ∙ unitVector u = ℂ ∙ u := by
  apply Submodule.span_singleton_smul_eq
  apply isUnit_iff_ne_zero.mpr
  simp [hu]

private lemma even_kernelString_spans (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) {v : V}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hne : v ≠ 0)
    (hzero : weightString J v (2 * j + 1) = 0) :
    LinearMap.ker J.Jx = ℂ ∙ unitVector (kernelString J v j (-1)) ∧
      LinearMap.ker J.Jy = ℂ ∙ unitVector (kernelString J v j 1) := by
  rw [unitVector_span (kernelString_nonzero J hv hne (-1)),
    unitVector_span (kernelString_nonzero J hv hne 1)]
  constructor
  · exact eq_span_singleton_of_mem_of_finrank_eq_one
      (even_ker_finrank (cycle J) (cycle_irreducible J hJ) hn)
      (kernelString_x_mem J hv hp hzero) (kernelString_nonzero J hv hne (-1))
  · exact eq_span_singleton_of_mem_of_finrank_eq_one
      (even_ker_finrank (cycle (cycle J))
        (cycle_irreducible (cycle J) (cycle_irreducible J hJ)) hn)
      (kernelString_y_mem J hv hp hzero) (kernelString_nonzero J hv hne 1)

private lemma kernel_amplitude_step (J : AngularMomentum V) {v : V} {j m : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hm : m < j) :
    kernelCoefficient j (m + 1) ^ 2 * ‖weightString J v (2 * (m + 1))‖ ^ 2 *
      ((2 * m + 2) * (2 * j - 2 * m - 1) : ℝ) =
    kernelCoefficient j m ^ 2 * ‖weightString J v (2 * m)‖ ^ 2 *
      ((2 * m + 1) * (2 * j - 2 * m) : ℝ) := by
  have hc := kernelCoefficient_step j m hm
  have h1 := weightString_norm J (μ := j) hv hp (2 * m)
  have h2 := weightString_norm J (μ := j) hv hp (2 * m + 1)
  have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [hidx, h2, h1]
  push_cast
  have ha : (2 * (m : ℝ) + 1 + 1) * (2 * j - (2 * m + 1)) =
      (2 * m + 2) * (2 * j - 2 * m - 1) := by ring
  rw [ha]
  calc
    _ = (kernelCoefficient j (m + 1) *
        ((2 * m + 2) * (2 * j - 2 * m - 1))) ^ 2 *
        ‖weightString J v (2 * m)‖ ^ 2 * ((2 * m + 1) * (2 * j - 2 * m)) := by ring
    _ = _ := by rw [hc]

private lemma kernel_amplitude_binomial (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1)
    (m : ℕ) (hm : m ≤ j) :
    kernelCoefficient j m ^ 2 * ‖weightString J v (2 * m)‖ ^ 2 =
      (Nat.centralBinom m : ℝ) * Nat.centralBinom (j - m) / Nat.centralBinom j := by
  induction m with
  | zero => simp [kernelCoefficient, weightString_zero, hnorm, Nat.centralBinom_ne_zero]
  | succ m ih =>
    have hm' : m < j := by omega
    have hstep := kernel_amplitude_step J hv hp hm'
    rw [ih (by omega)] at hstep
    have hmcast : (j - (m + 1) : ℕ) + 1 = j - m := by omega
    have hleft : ((m : ℝ) + 1) * Nat.centralBinom (m + 1) =
        2 * (2 * m + 1) * Nat.centralBinom m := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have hright : (((j - (m + 1) : ℕ) : ℝ) + 1) * Nat.centralBinom (j - m) =
        2 * (2 * ((j - (m + 1) : ℕ) : ℝ) + 1) * Nat.centralBinom (j - (m + 1)) := by
      have h := Nat.succ_mul_centralBinom_succ (j - (m + 1))
      rw [← hmcast]
      exact_mod_cast h
    have hsub : ((j - (m + 1) : ℕ) : ℝ) = (j : ℝ) - m - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      ring
    rw [hsub] at hright
    have hden : ((2 * m + 2) * (2 * j - 2 * m - 1) : ℝ) ≠ 0 := by
      have hlt : (m : ℝ) + 1 ≤ j := by exact_mod_cast hm'
      apply ne_of_gt
      apply mul_pos <;> linarith
    have hj : (Nat.centralBinom j : ℝ) ≠ 0 := by
      exact_mod_cast Nat.centralBinom_ne_zero j
    apply (mul_right_cancel₀ hden)
    rw [hstep]
    field_simp
    linear_combination
      (Nat.centralBinom m : ℝ) * (2 * m + 1) * hright -
      (Nat.centralBinom (j - (m + 1)) : ℝ) * (2 * ((j : ℝ) - m) - 1) * hleft

private lemma kernelString_inner (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (ε η : ℝ) :
    ⟪kernelString J v j ε, kernelString J v j η⟫_ℂ =
      ((∑ m ∈ Finset.range (j + 1), (ε * η) ^ m * kernelCoefficient j m ^ 2 *
        ‖weightString J v (2 * m)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [kernelString, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_eq_single m]
  · simp only [inner_self_eq_norm_sq_to_K]
    push_cast
    ring_nf
    rfl
  · intro l _ hl
    have horth := weightString_orthogonal J (μ := j) hv
      (show 2 * l ≠ 2 * m by omega)
    simp [horth]
  · exact fun h => (h hm).elim

private lemma kernelString_inner_binomial (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1)
    (ε η : ℝ) :
    ⟪kernelString J v j ε, kernelString J v j η⟫_ℂ =
      (((∑ m ∈ Finset.range (j + 1), (ε * η) ^ m *
        Nat.centralBinom m * Nat.centralBinom (j - m) : ℝ) / Nat.centralBinom j : ℝ) : ℂ) := by
  rw [kernelString_inner J hv]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_assoc, kernel_amplitude_binomial J hv hp hnorm m (by simpa using hm)]
  ring

private lemma kernelString_norm_sq (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1)
    {ε : ℝ} (hε : ε ^ 2 = 1) :
    ‖kernelString J v j ε‖ ^ 2 = (4 : ℝ) ^ j / Nat.centralBinom j := by
  have hinner := kernelString_inner_binomial J hv hp hnorm ε ε
  have hconv : (∑ m ∈ Finset.range (j + 1),
      (Nat.centralBinom m : ℝ) * Nat.centralBinom (j - m)) = (4 : ℝ) ^ j := by
    exact_mod_cast centralBinom_convolution j
  have hε' : ε * ε = 1 := by nlinarith [hε]
  simp only [hε', one_pow, one_mul, hconv, inner_self_eq_norm_sq_to_K] at hinner
  change (‖kernelString J v j ε‖ : ℂ) ^ 2 = _ at hinner
  rw [← Complex.ofReal_pow] at hinner
  exact Complex.ofReal_injective hinner

private lemma kernelString_xy_odd (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1)
    (hodd : Odd j) :
    ⟪kernelString J v j (-1), kernelString J v j 1⟫_ℂ = 0 := by
  rw [kernelString_inner_binomial J hv hp hnorm]
  have hconv : (∑ m ∈ Finset.range (j + 1),
      (-1 : ℝ) ^ m * Nat.centralBinom m * Nat.centralBinom (j - m)) = 0 := by
    exact_mod_cast centralBinom_alt_convolution_odd hodd
  simpa using congrArg (fun a : ℝ => ((a / Nat.centralBinom j : ℝ) : ℂ)) hconv

private lemma kernelString_xy_even (J : AngularMomentum V) {v : V} {k : ℕ}
    (hv : J.Jz v = ((2 * k : ℕ) : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1) :
    ⟪kernelString J v (2 * k) (-1), kernelString J v (2 * k) 1⟫_ℂ =
      (((4 : ℝ) ^ k * Nat.centralBinom k / Nat.centralBinom (2 * k) : ℝ) : ℂ) := by
  rw [kernelString_inner_binomial J hv hp hnorm]
  have hconv : (∑ m ∈ Finset.range (2 * k + 1),
      (-1 : ℝ) ^ m * Nat.centralBinom m * Nat.centralBinom (2 * k - m)) =
        (4 : ℝ) ^ k * Nat.centralBinom k := by
    exact_mod_cast centralBinom_alt_convolution_even k
  simpa using congrArg (fun a : ℝ => ((a / Nat.centralBinom (2 * k) : ℝ) : ℂ)) hconv

private lemma odd_kacT_zero (J : AngularMomentum V) (hJ : J.Irreducible)
    {n : ℕ} (hn : Module.finrank ℂ V = n + 1) (hodd : Odd n) : kacT J = 0 := by
  have hz := odd_weight_ker J hJ hn hodd
  have hx := odd_weight_ker (cycle J) (cycle_irreducible J hJ) hn hodd
  have hy := odd_weight_ker (cycle (cycle J))
    (cycle_irreducible (cycle J) (cycle_irreducible J hJ)) hn hodd
  change LinearMap.ker J.Jx = ⊥ at hx
  change LinearMap.ker J.Jy = ⊥ at hy
  simp [kacT, hx, hy, hz]

private lemma finrank_one_kacT (J : AngularMomentum V) (hJ : J.Irreducible)
    (hn : Module.finrank ℂ V = 1) : kacT J = LinearMap.id := by
  obtain ⟨b, hb⟩ := irreducible_weight_basis J hJ (n := 0) hn
  have hz : J.Jz = 0 := by
    apply b.toBasis.ext
    intro k
    have hk : k = 0 := Fin.ext (by omega)
    simpa [hk] using hb k
  have hx : J.Jx = 0 := by
    have h := J.comm_yz
    rw [hz] at h
    simp only [Ring.lie_def, mul_zero, zero_mul, sub_self] at h
    exact (smul_eq_zero.mp h.symm).resolve_left Complex.I_ne_zero
  have hy : J.Jy = 0 := by
    have h := J.comm_zx
    rw [hz] at h
    simp only [Ring.lie_def, mul_zero, zero_mul, sub_self] at h
    exact (smul_eq_zero.mp h.symm).resolve_left Complex.I_ne_zero
  ext f
  simp only [kacT, hx, hy, hz, LinearMap.ker_zero, Submodule.starProjection_top,
    LinearMap.smul_apply, ContinuousLinearMap.coe_coe, add_apply,
    ContinuousLinearMap.id_apply, LinearMap.id_apply]
  have ha : f + f + f = (3 : ℂ) • f := by module
  rw [ha, smul_smul]
  norm_num

private lemma kacT_symmetric (J : AngularMomentum V) : (kacT J).IsSymmetric := by
  apply LinearMap.IsSymmetric.smul (by simp only [map_inv₀, map_ofNat])
  exact ((LinearMap.ker J.Jx).starProjection_isSymmetric.add
    (LinearMap.ker J.Jy).starProjection_isSymmetric).add
      (LinearMap.ker J.Jz).starProjection_isSymmetric

private lemma kacT_nonnegative (J : AngularMomentum V) (f : V) :
    0 ≤ (⟪f, kacT J f⟫_ℂ).re := by
  have hx := (LinearMap.ker J.Jx).re_inner_starProjection_nonneg f
  have hy := (LinearMap.ker J.Jy).re_inner_starProjection_nonneg f
  have hz := (LinearMap.ker J.Jz).re_inner_starProjection_nonneg f
  rw [inner_re_symm] at hx hy hz
  change 0 ≤ (⟪f, (LinearMap.ker J.Jx).starProjection f⟫_ℂ).re at hx
  change 0 ≤ (⟪f, (LinearMap.ker J.Jy).starProjection f⟫_ℂ).re at hy
  change 0 ≤ (⟪f, (LinearMap.ker J.Jz).starProjection f⟫_ℂ).re at hz
  simp only [kacT, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    add_apply, inner_smul_right, inner_add_right]
  norm_num [Complex.mul_re, Complex.add_re]
  linarith

private lemma kernelString_norms_equal (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1) :
    ‖kernelString J v j (-1)‖ = ‖kernelString J v j 1‖ := by
  have hx := kernelString_norm_sq J hv hp hnorm (ε := -1) (by norm_num)
  have hy := kernelString_norm_sq J hv hp hnorm (ε := 1) (by norm_num)
  nlinarith [norm_nonneg (kernelString J v j (-1)), norm_nonneg (kernelString J v j 1)]

omit [FiniteDimensional ℂ V] in
private lemma unitVector_inner_equal_norm [FiniteDimensional ℂ V] (u w : V) (hnorm : ‖u‖ = ‖w‖) :
    ⟪unitVector u, unitVector w⟫_ℂ = ⟪u, w⟫_ℂ / ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [unitVector, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal, hnorm]
  push_cast
  simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
  ring

private lemma unitKernel_xy_odd (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1)
    (hodd : Odd j) :
    ⟪unitVector (kernelString J v j (-1)), unitVector (kernelString J v j 1)⟫_ℂ = 0 := by
  rw [unitVector_inner_equal_norm _ _ (kernelString_norms_equal J hv hp hnorm),
    kernelString_xy_odd J hv hp hnorm hodd, zero_div]

private lemma unitKernel_xy_even (J : AngularMomentum V) {v : V} {k : ℕ}
    (hv : J.Jz v = ((2 * k : ℕ) : ℂ) • v) (hp : raising J v = 0) (hnorm : ‖v‖ = 1) :
    ⟪unitVector (kernelString J v (2 * k) (-1)), unitVector (kernelString J v (2 * k) 1)⟫_ℂ =
      (centralOverlap k : ℂ) := by
  rw [unitVector_inner_equal_norm _ _ (kernelString_norms_equal J hv hp hnorm),
    kernelString_xy_even J hv hp hnorm,
    kernelString_norm_sq J hv hp hnorm (ε := 1) (by norm_num)]
  unfold centralOverlap
  have hj : (Nat.centralBinom (2 * k) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (2 * k)
  have hp4 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  rw [pow_mul]
  field_simp
  simp [← pow_mul, mul_comm]

private lemma kernelString_z_odd (J : AngularMomentum V) {v : V} {j : ℕ}
    (hv : J.Jz v = (j : ℂ) • v) (hodd : Odd j) (ε : ℝ) :
    ⟪unitVector (weightString J v j), kernelString J v j ε⟫_ℂ = 0 := by
  change ⟪(‖weightString J v j‖⁻¹ : ℂ) • weightString J v j, _⟫_ℂ = _
  rw [inner_smul_left]
  have hs : (∑ m ∈ Finset.range (j + 1),
      ((ε ^ m * kernelCoefficient j m : ℝ) : ℂ) *
        ⟪weightString J v j, weightString J v (2 * m)⟫_ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    have hne : j ≠ 2 * m := by obtain ⟨r, hr⟩ := hodd; omega
    rw [weightString_orthogonal J (μ := j) hv hne, mul_zero]
  change (starRingEnd ℂ) (‖weightString J v j‖⁻¹ : ℂ) * _ = 0
  simp only [kernelString, inner_sum, inner_smul_right, hs, mul_zero]

private lemma kernelString_z_even (J : AngularMomentum V) {v : V} {k : ℕ}
    (hv : J.Jz v = ((2 * k : ℕ) : ℂ) • v)
    (hne : weightString J v (2 * k) ≠ 0) (ε : ℝ) :
    ⟪unitVector (weightString J v (2 * k)), kernelString J v (2 * k) ε⟫_ℂ =
      ((ε ^ k * kernelCoefficient (2 * k) k * ‖weightString J v (2 * k)‖ : ℝ) : ℂ) := by
  simp only [unitVector, kernelString, inner_smul_left, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single k]
  · simp only [inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal]
    have hnorm : (‖weightString J v (2 * k)‖ : ℂ) ≠ 0 := by simp [hne]
    push_cast
    field_simp
    ring_nf
    rfl
  · intro m _ hm
    rw [weightString_orthogonal J (μ := (2 * k : ℕ)) hv (show 2 * k ≠ 2 * m by omega), mul_zero]
    simp
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

private lemma kernel_middle_ratio (J : AngularMomentum V) {v : V} {k : ℕ}
    (hv : J.Jz v = ((2 * k : ℕ) : ℂ) • v) (hp : raising J v = 0)
    (hnorm : ‖v‖ = 1) :
    kernelCoefficient (2 * k) k * ‖weightString J v (2 * k)‖ /
      ‖kernelString J v (2 * k) 1‖ = centralOverlap k := by
  have hne : v ≠ 0 := by intro h; simp [h] at hnorm
  have hN : 0 < ‖kernelString J v (2 * k) 1‖ :=
    norm_pos_iff.mpr (kernelString_nonzero J hv hne 1)
  have ha := kernel_amplitude_binomial J hv hp hnorm k (by omega)
  have hn := kernelString_norm_sq J hv hp hnorm (ε := 1) (by norm_num)
  have hj : (Nat.centralBinom (2 * k) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (2 * k)
  have hk : (0 : ℝ) ≤ kernelCoefficient (2 * k) k :=
    (kernelCoefficient_positive (2 * k) k (by omega)).le
  have hA : (kernelCoefficient (2 * k) k * ‖weightString J v (2 * k)‖) ^ 2 =
      centralOverlap k ^ 2 * ‖kernelString J v (2 * k) 1‖ ^ 2 := by
    rw [mul_pow, ha, hn]
    unfold centralOverlap
    have hsub : 2 * k - k = k := by omega
    rw [hsub, pow_mul]
    field_simp
    simp [← pow_mul, Nat.mul_comm]
  have hpos := (centralOverlap_pos k).le
  have heq : kernelCoefficient (2 * k) k * ‖weightString J v (2 * k)‖ =
      centralOverlap k * ‖kernelString J v (2 * k) 1‖ := by
    nlinarith [norm_nonneg (weightString J v (2 * k)),
      mul_nonneg hk (norm_nonneg (weightString J v (2 * k))), mul_nonneg hpos hN.le]
  rw [heq, mul_div_cancel_right₀ _ (ne_of_gt hN)]

private lemma unitKernel_z_even (J : AngularMomentum V) {v : V} {k : ℕ}
    (hv : J.Jz v = ((2 * k : ℕ) : ℂ) • v) (hp : raising J v = 0)
    (hnorm : ‖v‖ = 1) (hne : weightString J v (2 * k) ≠ 0) :
    ⟪unitVector (weightString J v (2 * k)), unitVector (kernelString J v (2 * k) (-1))⟫_ℂ =
      (((-1 : ℝ) ^ k * centralOverlap k : ℝ) : ℂ) ∧
    ⟪unitVector (weightString J v (2 * k)), unitVector (kernelString J v (2 * k) 1)⟫_ℂ =
      (centralOverlap k : ℂ) := by
  have hratio := kernel_middle_ratio J hv hp hnorm
  have heq := kernelString_norms_equal J hv hp hnorm
  constructor
  · simp only [unitVector, inner_smul_right]
    change (‖kernelString J v (2 * k) (-1)‖⁻¹ : ℂ) *
      ⟪unitVector (weightString J v (2 * k)), kernelString J v (2 * k) (-1)⟫_ℂ = _
    rw [kernelString_z_even J hv hne, heq]
    have h : ‖kernelString J v (2 * k) 1‖⁻¹ *
        ((-1 : ℝ) ^ k * kernelCoefficient (2 * k) k * ‖weightString J v (2 * k)‖) =
          (-1 : ℝ) ^ k * centralOverlap k := by
      rw [← hratio]
      ring
    exact_mod_cast h
  · change ⟪unitVector (weightString J v (2 * k)),
      (‖kernelString J v (2 * k) 1‖⁻¹ : ℂ) • kernelString J v (2 * k) 1⟫_ℂ = _
    rw [inner_smul_right, kernelString_z_even J hv hne]
    simp only [one_pow, one_mul]
    rw [← hratio]
    push_cast
    ring

omit [FiniteDimensional ℂ V] in
private lemma real_inner_reverse [FiniteDimensional ℂ V] {x y : V} {r : ℝ} (h : ⟪x, y⟫_ℂ = (r : ℂ)) :
    ⟪y, x⟫_ℂ = (r : ℂ) := by
  rw [← inner_conj_symm y x, h, Complex.conj_ofReal]

/-- For integer spin, phase choices make all three overlaps equal to the
manuscript coefficient `a_j`. The weight-string construction realizes the
three zero-weight lines used in the manuscript's Gram matrix. -/
theorem nonempty_axisKernelVectors_of_integer_spin (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) :
    Nonempty (AxisKernelVectors J (spinOverlap j)) := by
  classical
  obtain ⟨v, hnorm, hv, hp, hne, hzero, hspan⟩ := irreducible_string_basis J hJ hn
  have hμ : ((2 * j : ℕ) : ℝ) / 2 = (j : ℝ) := by push_cast; ring
  have hv' : J.Jz v = (j : ℂ) • v := by rw [hμ] at hv; simpa using hv
  have hvne : v ≠ 0 := by intro h; simp [h] at hnorm
  let x := unitVector (kernelString J v j (-1))
  let y := unitVector (kernelString J v j 1)
  let z := unitVector (weightString J v j)
  have hx : ‖x‖ = 1 := unitVector_norm (kernelString_nonzero J hv' hvne (-1))
  have hy : ‖y‖ = 1 := unitVector_norm (kernelString_nonzero J hv' hvne 1)
  have hz : ‖z‖ = 1 := unitVector_norm (hne j (by omega))
  obtain ⟨hkx, hky⟩ := even_kernelString_spans J hJ hn hv' hp hvne hzero
  let b := OrthonormalBasis.mk (normalizedString_orthonormal J hv hne) hspan.ge
  have hb (k : Fin (2 * j + 1)) : J.Jz (b k) = (((j : ℝ) - k : ℝ) : ℂ) • b k := by
    have h := normalizedString_weight J hv k
    rw [hμ] at h
    simpa [b] using h
  have hkz : LinearMap.ker J.Jz = ℂ ∙ z := by
    rw [even_weight_ker J b hb]
    simp [b, normalizedString, unitVector, z]
  rcases Nat.even_or_odd j with heven | hodd
  · obtain ⟨k, hk⟩ := heven
    have hjk : j = 2 * k := by omega
    clear hk
    subst j
    let ε : ℂ := ((-1 : ℝ) ^ k : ℂ)
    have hεnorm : ‖ε‖ = 1 := by simp [ε, norm_pow]
    have hεne : ε ≠ 0 := by intro h; simp [h] at hεnorm
    have hy' : ‖ε • y‖ = 1 := by rw [norm_smul, hεnorm, hy, one_mul]
    have hxy : ⟪x, y⟫_ℂ = (centralOverlap k : ℂ) :=
      unitKernel_xy_even J hv' hp hnorm
    have hzx : ⟪z, x⟫_ℂ = (((-1 : ℝ) ^ k * centralOverlap k : ℝ) : ℂ) ∧
        ⟪z, y⟫_ℂ = (centralOverlap k : ℂ) :=
      unitKernel_z_even J hv' hp hnorm (hne (2 * k) (by omega))
    have hxz : ⟪x, z⟫_ℂ = (spinOverlap (2 * k) : ℂ) :=
      real_inner_reverse (by simpa only [spinOverlap_even, centralOverlap] using hzx.1)
    have hxy' : ⟪x, ε • y⟫_ℂ = (spinOverlap (2 * k) : ℂ) := by
      rw [inner_smul_right, hxy, spinOverlap_even]
      simp [ε, centralOverlap]
    have hyz : ⟪ε • y, z⟫_ℂ = (spinOverlap (2 * k) : ℂ) := by
      rw [inner_smul_left, real_inner_reverse hzx.2, spinOverlap_even]
      simp [ε, centralOverlap]
    refine ⟨{ vector := ![x, ε • y, z]
              unit := ?_
              kernel_x := hkx
              kernel_y := ?_
              kernel_z := hkz
              gram := ?_ }⟩
    · intro a
      fin_cases a <;> simp [hx, hy', hz]
    · change LinearMap.ker J.Jy = ℂ ∙ (ε • y)
      rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hεne)]
      exact hky
    · intro a b
      have hyx := real_inner_reverse hxy'
      have hzx' := real_inner_reverse hxz
      have hzy := real_inner_reverse hyz
      fin_cases a <;> fin_cases b <;>
        simp [inner_self_eq_norm_sq_to_K, hx, hy', hz, hxy', hxz, hyz, hyx, hzx', hzy]
  · have hxy : ⟪x, y⟫_ℂ = 0 := unitKernel_xy_odd J hv' hp hnorm hodd
    have hzx : ⟪z, x⟫_ℂ = 0 := by
      change ⟪z, (‖kernelString J v j (-1)‖⁻¹ : ℂ) • kernelString J v j (-1)⟫_ℂ = 0
      rw [inner_smul_right, kernelString_z_odd J hv' hodd, mul_zero]
    have hzy : ⟪z, y⟫_ℂ = 0 := by
      change ⟪z, (‖kernelString J v j 1‖⁻¹ : ℂ) • kernelString J v j 1⟫_ℂ = 0
      rw [inner_smul_right, kernelString_z_odd J hv' hodd, mul_zero]
    refine ⟨{ vector := ![x, y, z]
              unit := ?_
              kernel_x := hkx
              kernel_y := hky
              kernel_z := hkz
              gram := ?_ }⟩
    · intro a
      fin_cases a <;> simp [hx, hy, hz]
    · intro a b
      have hyx : ⟪y, x⟫_ℂ = 0 := by simpa using real_inner_reverse (r := 0) hxy
      have hxz : ⟪x, z⟫_ℂ = 0 := by simpa using real_inner_reverse (r := 0) hzx
      have hyz : ⟪y, z⟫_ℂ = 0 := by simpa using real_inner_reverse (r := 0) hzy
      fin_cases a <;> fin_cases b <;>
        simp [inner_self_eq_norm_sq_to_K, hx, hy, hz, hxy, hxz, hyz, hyx, hzx, hzy,
          spinOverlap_odd hodd]

/-- The manuscript's exact nonzero Kac eigenvalues on an integer-spin irreducible. -/
theorem kacT_hasEigenvalue_iff_of_integer_spin (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (kacT J) μ ↔
      μ = (((1 + 2 * spinOverlap j) / 3 : ℝ) : ℂ) ∨
        μ = (((1 - spinOverlap j) / 3 : ℝ) : ℂ) := by
  obtain ⟨D⟩ := nonempty_axisKernelVectors_of_integer_spin J hJ hn
  exact D.hasEigenvalue_iff hμ

/-- Exact nonzero spectral values on an integer-spin irreducible. -/
theorem kacT_mem_spectrum_iff_of_integer_spin (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) {μ : ℂ} (hμ : μ ≠ 0) :
    μ ∈ spectrum ℂ (kacT J) ↔
      μ = (((1 + 2 * spinOverlap j) / 3 : ℝ) : ℂ) ∨
        μ = (((1 - spinOverlap j) / 3 : ℝ) : ℂ) := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  exact kacT_hasEigenvalue_iff_of_integer_spin J hJ hn hμ

/-- The maximum eigenvalue is exactly `λ_j`, as computed from the three-by-three Gram matrix. -/
theorem kacT_isGreatest_eigenvalue_of_integer_spin (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) :
    IsGreatest {r : ℝ | Module.End.HasEigenvalue (kacT J) (r : ℂ)} (spinKacMaximum j) := by
  obtain ⟨D⟩ := nonempty_axisKernelVectors_of_integer_spin J hJ hn
  exact D.isGreatest_eigenvalue

/-- Every real eigenvalue in integer spin at least six lies strictly below `7/12`. -/
theorem kacT_eigenvalue_lt_of_six_le (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) (hj : 6 ≤ j)
    {r : ℝ} (hr : Module.End.HasEigenvalue (kacT J) (r : ℂ)) : r < 7 / 12 :=
  lt_of_le_of_lt ((kacT_isGreatest_eigenvalue_of_integer_spin J hJ hn).2 hr)
    (spinKacMaximum_lt_of_six_le hj)

/-- The exact integer-spin maximum bounds each quadratic form. -/
theorem kacT_quadratic_le_of_integer_spin (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) (f : V) :
    (⟪f, kacT J f⟫_ℂ).re ≤ spinKacMaximum j * ‖f‖ ^ 2 := by
  obtain ⟨D⟩ := nonempty_axisKernelVectors_of_integer_spin J hJ hn
  exact D.quadratic_le f

private lemma even_form_bound (J : AngularMomentum V) (hJ : J.Irreducible)
    {j : ℕ} (hn : Module.finrank ℂ V = 2 * j + 1) (hj : 0 < j) :
    ∀ f : V, (⟪f, kacT J f⟫_ℂ).re ≤ (7 / 12 : ℝ) * ‖f‖ ^ 2 := by
  intro f
  exact (kacT_quadratic_le_of_integer_spin J hJ hn f).trans
    (mul_le_mul_of_nonneg_right (spinKacMaximum_le hj) (sq_nonneg ‖f‖))

private lemma gap_of_form_bound (J : AngularMomentum V)
    (hbound : ∀ f : V, (⟪f, kacT J f⟫_ℂ).re ≤ (7 / 12 : ℝ) * ‖f‖ ^ 2) :
    KacGapOn J := by
  classical
  let T := kacT J
  have hT : T.IsSymmetric := kacT_symmetric J
  let b := hT.eigenvectorBasis rfl
  let t := hT.eigenvalues rfl
  have ht (i : Fin (Module.finrank ℂ V)) : t i ≤ (7 / 12 : ℝ) := by
    have h := hbound (b i)
    have he := hT.apply_eigenvectorBasis rfl i
    change T (b i) = (t i : ℂ) • b i at he
    change (⟪b i, T (b i)⟫_ℂ).re ≤ _ at h
    rw [he, inner_smul_right] at h
    simpa [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one] using h
  let Q : Module.End ℂ V := (T - LinearMap.id) ∘ₗ
    (T - (((7 / 12 : ℝ) : ℂ) • LinearMap.id))
  have hdiag (f : V) (i : Fin (Module.finrank ℂ V)) :
      b.repr (Q f) i =
        (((t i - 1) * (t i - 7 / 12) : ℝ) : ℂ) * b.repr f i := by
    have hcoord (g : V) : b.repr (T g) i = (t i : ℂ) * b.repr g i :=
      hT.eigenvectorBasis_apply_self_apply rfl g i
    simp only [Q, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
      hcoord, smul_eq_mul]
    push_cast
    ring
  intro f
  change 0 ≤ (⟪f, Q f⟫_ℂ).re
  rw [← b.sum_inner_mul_inner f (Q f), Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [← b.repr_apply_apply, hdiag]
  have hprod : 0 ≤ (t i - 1) * (t i - 7 / 12) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith [ht i]) (by linarith [ht i])
  rw [b.repr_apply_apply]
  have he : ⟪f, b i⟫_ℂ *
      ((((t i - 1) * (t i - 7 / 12) : ℝ) : ℂ) * ⟪b i, f⟫_ℂ) =
      (((t i - 1) * (t i - 7 / 12) : ℝ) : ℂ) *
        (⟪f, b i⟫_ℂ * ⟪b i, f⟫_ℂ) := by ring
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg hprod
  rw [← Complex.mul_re]
  change 0 ≤ RCLike.re (⟪f, b i⟫_ℂ * ⟪b i, f⟫_ℂ)
  rw [inner_mul_symm_re_eq_norm]
  positivity

private lemma gap_of_identity (J : AngularMomentum V) (h : kacT J = LinearMap.id) :
    KacGapOn J := by
  intro f
  simp [h]

private lemma gap_of_finrank_zero (J : AngularMomentum V)
    (hn : Module.finrank ℂ V = 0) : KacGapOn J := by
  intro f
  rw [(finrank_zero_iff_forall_zero.mp hn) f]
  simp

/-- Polynomial gap inequality for an irreducible angular-momentum triple.

In dimension `n + 1`, successive applications of the lowering operator to a
highest-weight vector give an orthonormal weight basis after normalization.
The weights are `n/2 - k` for `0 ≤ k ≤ n`, and the coefficient connecting
consecutive basis vectors is `√((k+1)(n-k))`.

When `n` is odd the three axis generators have zero kernels, so `kacT J = 0`.
For `n = 2j > 0`, each kernel is one-dimensional. Its normalized spanning
vector is computed in the weight basis and phase-normalized so that all
three pairwise overlaps equal the manuscript coefficient `a_j`. This is zero
for odd `j`, and `(-1)^k centralBinom k / 4^k` for `j = 2k`. The exact nonzero
eigenvalues are `(1 + 2a_j)/3` and `(1 - a_j)/3`. Their maximum `λ_j` is
`1/2` at `j = 2`, `7/12` at `j = 4`, and strictly smaller than `7/12` for
`j ≥ 6`. The exact maximum therefore bounds the quadratic form by
`(7/12) ‖f‖²` on every nontrivial integer-spin irreducible.

The symmetric spectral decomposition then gives `(T-I)(T-(7/12)I) ≥ 0`.
In dimension one `T = I`, and in dimension zero the form vanishes.
-/
theorem kacGapOn_of_irreducible (J : AngularMomentum V) (hJ : J.Irreducible) :
    KacGapOn J := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℂ V = n := ⟨_, rfl⟩
  cases n with
  | zero => exact gap_of_finrank_zero J hn
  | succ n =>
    cases n with
    | zero => exact gap_of_identity J (finrank_one_kacT J hJ hn)
    | succ n =>
      rcases Nat.even_or_odd (n + 1) with heven | hodd
      · obtain ⟨j, hj⟩ := heven
        have hdim : Module.finrank ℂ V = 2 * j + 1 := by omega
        exact gap_of_form_bound J (even_form_bound J hJ hdim (by omega))
      · apply gap_of_form_bound
        intro f
        rw [odd_kacT_zero J hJ hn hodd]
        simp

/-- The spectral gap for every triple, by strong induction on the dimension. -/
theorem kacGapOn_all (J : AngularMomentum V) : KacGapOn J := by
  suffices h : ∀ n (W : Type _) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
      [FiniteDimensional ℂ W], Module.finrank ℂ W = n →
      ∀ A : AngularMomentum W, KacGapOn A by
    exact h _ V rfl J
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ _ hn A
    by_cases hirr : A.Irreducible
    · exact kacGapOn_of_irreducible A hirr
    · simp only [Irreducible, not_forall, not_or] at hirr
      obtain ⟨U, hU, hbot, htop⟩ := hirr
      apply kacGapOn_of_split A hU
      · exact ih (Module.finrank ℂ U) (hn ▸ Submodule.finrank_lt htop)
          U rfl (A.restrictJ U hU)
      · have hotop : Uᗮ ≠ ⊤ := fun h => hbot (U.orthogonal_eq_top_iff.mp h)
        exact ih (Module.finrank ℂ Uᗮ) (hn ▸ Submodule.finrank_lt hotop)
          Uᗮ rfl (A.restrictJ Uᗮ (A.invariant_orthogonal hU))

end AngularMomentum

end

end GaussianTesting
