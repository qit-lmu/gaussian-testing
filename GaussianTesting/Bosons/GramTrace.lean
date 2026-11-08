module

/-
Copyright (c) 2026 Jop Briët, Davi Castro-Silva, Michael Walter, Freek Witteveen.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import GaussianTesting.Bosons.Mixed

@[expose] public section

/-!
# Basis-independent trace of Gram operators

For every summable Gram family, the diagonal of its operator in any Hilbert
basis has sum equal to the total squared norm of the family. This is the
trace identity needed to relate Gram operators to positive trace-class operators.
-/

namespace GaussianTesting

open scoped InnerProductSpace

set_option maxHeartbeats 1600000

variable {ι κ ι' E : Type*}

/-- Parseval's identity, with the vector in the first slot of the inner product. -/
theorem hilbertBasis_hasSum_norm_inner_sq [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : HilbertBasis ι' ℂ E) (x : E) :
    HasSum (fun j => ‖inner ℂ x (b j)‖ ^ 2) (‖x‖ ^ 2) := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner x x)
  convert h using 1
  · ext j
    rw [← inner_conj_symm (b j) x, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  · exact norm_sq_eq_re_inner (𝕜 := ℂ) x

/-- Every Hilbert basis gives the same finite trace for a Gram operator. -/
theorem gramOp_hasSum_diagonal {g : ι → L2 κ} (hg : GramFam g)
    (b : HilbertBasis ι' ℂ (L2 κ)) :
    HasSum (fun j => (inner ℂ (b j) (gramOp g hg (b j))).re)
      (∑' i, ‖g i‖ ^ 2) := by
  have hrow (i : ι) := hilbertBasis_hasSum_norm_inner_sq b (g i)
  have hd : Summable (fun p : ι × ι' => ‖inner ℂ (g p.1) (b p.2)‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
    refine ⟨fun i => (hrow i).summable, ?_⟩
    simpa only [GramFam, (hrow _).tsum_eq] using hg
  have hs := hd.prod_symm.prod.hasSum
  change HasSum (fun j => ∑' i, ‖inner ℂ (g i) (b j)‖ ^ 2)
    (∑' j, ∑' i, ‖inner ℂ (g i) (b j)‖ ^ 2) at hs
  have he : (∑' j, ∑' i, ‖inner ℂ (g i) (b j)‖ ^ 2) = ∑' i, ‖g i‖ ^ 2 := by
    rw [Summable.tsum_comm (f := fun i j => ‖inner ℂ (g i) (b j)‖ ^ 2) hd]
    simp only [(hrow _).tsum_eq]
  rw [he] at hs
  simpa only [inner_gramOp_self hg, Complex.ofReal_re] using hs

end GaussianTesting
