module

/-
The central-binomial convolution identities used to compute the overlaps of
the axis kernels in `Kac/Gap.lean`. Write `cₘ = C(2m,m)`. Then

* `centralBinom_convolution` proves `∑_{m=0}^n cₘ c_{n−m} = 4ⁿ`.
* `centralBinom_alt_convolution_odd` and `centralBinom_alt_convolution_even`
  evaluate `Eₙ = ∑_{m=0}^n (-1)^m cₘ c_{n−m}`. It vanishes for odd `n`
  and equals `4ᵏ cₖ` for `n = 2k`.

The first identity follows from the generalized Chu–Vandermonde identity
at `r = s = −1/2` over `ℚ`, using
`Ring.choose (-1/2 : ℚ) m = (-1/4)^m * C(2m,m)`.
For the second identity, reindexing `m ↦ n−m` shows that `Eₙ = 0` for odd `n`.
The convolution `∑_{i+j=n} Eᵢ Eⱼ` equals `4ⁿ` for even `n` and vanishes for
odd `n`. Consequently `Gₖ = E₂ₖ` satisfies `G₀ = 1` and
`∑_{p+q=k} Gₚ G_q = 16ᵏ`. The sequence `4ᵏ cₖ` satisfies the same recurrence,
which determines `Gₖ` by induction.
-/
public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace GaussianTesting

open Finset

private lemma choose_step (r : ℚ) (n : ℕ) :
    (n + 1 : ℚ) * Ring.choose r (n+1) = (r - n) * Ring.choose r n := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose r (n+1)
  rw [descPochhammer_succ_right] at h
  simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, pow_one, pow_zero, nsmul_eq_mul,
    Ring.descPochhammer_eq_factorial_smul_choose] at h
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] at h
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  linear_combination -h

/-- `Ring.choose (-1/2) m = (-1/4)^m * C(2m, m)` over ℚ. -/
lemma ring_choose_neg_half (m : ℕ) :
    Ring.choose (-(1 / 2) : ℚ) m = (-(1 / 4) : ℚ) ^ m * Nat.centralBinom m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := choose_step (-(1/2)) m
    have hc := congrArg (fun a : ℕ => (a : ℚ)) (Nat.succ_mul_centralBinom_succ m)
    push_cast at hc
    rw [ih] at h
    rw [pow_succ]
    have hm : (m + 1 : ℚ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hm
    linear_combination h + (-(1/4) : ℚ)^m / 4 * hc

/-- The central binomial convolution `Σ C(2m,m) C(2(n-m),n-m) = 4^n`. -/
theorem centralBinom_convolution (n : ℕ) :
    ∑ m ∈ range (n + 1), (Nat.centralBinom m * Nat.centralBinom (n - m) : ℚ)
      = 4 ^ n := by
  have hneg (j : ℕ) : Ring.choose (-1 : ℚ) j = (-1 : ℚ)^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := choose_step (-1) j
      rw [ih] at h
      rw [pow_succ]
      have hj : (j + 1 : ℚ) ≠ 0 := by positivity
      apply mul_left_cancel₀ hj
      linear_combination h
  have h := Ring.add_choose_eq (R := ℚ) n (Commute.all (-(1/2) : ℚ) (-(1/2)))
  rw [show (-(1/2) : ℚ) + -(1/2) = -1 by norm_num, hneg,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [ring_choose_neg_half] at h
  have hs : ∑ m ∈ range (n+1),
      ((-(1/4) : ℚ)^m * ↑(Nat.centralBinom m) *
       ((-(1/4) : ℚ)^(n-m) * ↑(Nat.centralBinom (n-m)))) =
      (-(1/4) : ℚ)^n * ∑ m ∈ range (n+1),
        (Nat.centralBinom m * Nat.centralBinom (n-m) : ℚ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    have hm' : m ≤ n := mem_range_succ_iff.mp hm
    have hp : (-(1/4) : ℚ)^n = (-(1/4) : ℚ)^m * (-(1/4) : ℚ)^(n-m) := by
      rw [← pow_add, Nat.add_sub_of_le hm']
    rw [hp]
    ring
  rw [hs] at h
  apply mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-(1/4) : ℚ) ≠ 0))
  rw [← h, ← mul_pow]
  norm_num

/-- The alternating central-binomial convolution vanishes in odd degree. -/
theorem centralBinom_alt_convolution_odd {n : ℕ} (hn : Odd n) :
    ∑ m ∈ range (n + 1),
      ((-1 : ℚ) ^ m * Nat.centralBinom m * Nat.centralBinom (n - m)) = 0 := by
  let f : ℕ → ℚ := fun m => (-1)^m * Nat.centralBinom m * Nat.centralBinom (n-m)
  have href := Finset.sum_range_reflect f (n+1)
  have heq : ∑ m ∈ range (n+1), f (n+1-1-m) =
      -(∑ m ∈ range (n+1), f m) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro m hm
    have hm' : m ≤ n := mem_range_succ_iff.mp hm
    have hp : (-1 : ℚ)^(n-m) = -(-1 : ℚ)^m := by
      have h : (-1 : ℚ)^(n-m) * (-1 : ℚ)^m = -1 := by
        rw [← pow_add, Nat.sub_add_cancel hm', hn.neg_one_pow]
      have hsq : (-1 : ℚ)^m * (-1 : ℚ)^m = 1 := by
        rw [← mul_pow]; norm_num
      calc
        _ = ((-1 : ℚ)^(n-m) * (-1 : ℚ)^m) * (-1 : ℚ)^m := by rw [mul_assoc, hsq, mul_one]
        _ = _ := by rw [h]; ring
    dsimp [f]
    simp only [Nat.sub_sub_self hm', hp]
    ring
  linarith

private def conv (x y : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ range (n+1), x m * y (n-m)

private lemma conv_deriv (x y : ℕ → ℚ) (n : ℕ) :
    (n+1 : ℚ) * conv x y (n+1) =
      conv (fun m => (m+1 : ℚ) * x (m+1)) y n +
      conv x (fun m => (m+1 : ℚ) * y (m+1)) n := by
  unfold conv
  rw [mul_sum]
  have hsplit : ∑ m ∈ range (n+1+1), (n+1 : ℚ) * (x m * y (n+1-m)) =
      (∑ m ∈ range (n+1+1), (m : ℚ) * x m * y (n+1-m)) +
      ∑ m ∈ range (n+1+1), x m * ((n+1-m : ℕ) : ℚ) * y (n+1-m) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    have hm' : m ≤ n+1 := mem_range_succ_iff.mp hm
    push_cast [Nat.cast_sub hm']
    ring
  rw [hsplit, sum_range_succ' (fun m => (m : ℚ) * x m * y (n+1-m)),
    sum_range_succ (fun m => x m * ((n+1-m : ℕ) : ℚ) * y (n+1-m))]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.sub_self]
  congr 1
  · apply sum_congr rfl
    intro m hm
    simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one]
  · apply sum_congr rfl
    intro m hm
    have hm' : m ≤ n := mem_range_succ_iff.mp hm
    rw [show n+1-m = (n-m)+1 by omega, Nat.cast_add, Nat.cast_one]
    ring

private def cb (n : ℕ) : ℚ := Nat.centralBinom n
private def acb (n : ℕ) : ℚ := (-1)^n * cb n
private def alt (n : ℕ) : ℚ := conv acb cb n
private def moment (n : ℕ) : ℚ := conv (fun m => (m : ℚ) * acb m) cb n

private lemma cb_step (n : ℕ) : (n+1 : ℚ) * cb (n+1) = (4*n+2) * cb n := by
  have h := congrArg (fun a : ℕ => (a : ℚ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at h
  dsimp [cb]
  linear_combination h

private lemma acb_step (n : ℕ) : (n+1 : ℚ) * acb (n+1) = -(4*n+2) * acb n := by
  dsimp [acb]
  rw [pow_succ]
  linear_combination (-(-1 : ℚ)^n) * cb_step n

private lemma alt_deriv (n : ℕ) :
    (n+1 : ℚ) * alt (n+1) = 4*n * alt n - 8 * moment n := by
  rw [alt, conv_deriv]
  simp only [acb_step, cb_step]
  unfold conv alt moment conv
  rw [← sum_add_distrib, mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  have hm' : m ≤ n := mem_range_succ_iff.mp hm
  push_cast [Nat.cast_sub hm']
  ring

private lemma moment_step (n : ℕ) :
    moment (n+1) = -4 * moment n - 2 * alt n := by
  unfold moment conv
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  unfold alt conv
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [Nat.cast_add, Nat.cast_one, Nat.add_sub_add_right, acb_step]
  ring

private lemma alt_step (n : ℕ) :
    (n+2 : ℚ) * alt (n+2) = 16*(n+1) * alt n := by
  have h₁ := alt_deriv (n+1)
  have h₂ := alt_deriv n
  have h₃ := moment_step n
  push_cast at h₁
  linear_combination h₁ + 4*h₂ - 8*h₃

/-- The alternating central-binomial convolution in even degree satisfies `Σ (-1)^m C(2m,m) C(2(2k-m),2k-m) = 4^k C(2k,k)`. -/
theorem centralBinom_alt_convolution_even (k : ℕ) :
    ∑ m ∈ range (2 * k + 1),
      ((-1 : ℚ) ^ m * Nat.centralBinom m * Nat.centralBinom (2 * k - m))
      = 4 ^ k * Nat.centralBinom k := by
  change alt (2*k) = 4^k * cb k
  induction k with
  | zero => simp [alt, conv, acb, cb]
  | succ k ih =>
    have h := alt_step (2*k)
    rw [ih] at h
    have hc := cb_step k
    have hk : (2*(k+1) : ℚ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    rw [show 2*(k+1) = 2*k+2 by omega, pow_succ]
    push_cast at h ⊢
    linear_combination h - 8*(4 : ℚ)^k * hc

end GaussianTesting
