/-!
# Finite sums over an initial segment

Counting arguments need sums, and this project has no library, so `sumRange` is
defined here together with the handful of facts the density argument uses:
splitting a range, comparing sums pointwise, and pulling out a constant factor.

`sumRange n f` is `f 0 + f 1 + ⋯ + f (n-1)`.
-/

namespace Collatz
namespace Sum

/-- `sumRange n f = f 0 + ⋯ + f (n-1)`. -/
def sumRange : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumRange n f + f n

/-- The empty sum. -/
@[simp] theorem sumRange_zero (f : Nat → Nat) : sumRange 0 f = 0 := rfl

/-- Peeling off the last term. -/
theorem sumRange_succ (n : Nat) (f : Nat → Nat) :
    sumRange (n + 1) f = sumRange n f + f n := rfl

/-- A one-term sum. -/
@[simp] theorem sumRange_one (f : Nat → Nat) : sumRange 1 f = f 0 := by
  rw [sumRange_succ, sumRange_zero]
  omega

/-- Sums agree when the summands agree on the range. -/
theorem sumRange_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i = g i) :
    sumRange n f = sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Sums respect pointwise comparison. -/
theorem sumRange_le {n : Nat} {f g : Nat → Nat} (h : ∀ i, i < n → f i ≤ g i) :
    sumRange n f ≤ sumRange n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    omega

/-- Sums of sums. -/
theorem sumRange_add (n : Nat) (f g : Nat → Nat) :
    sumRange n (fun i => f i + g i) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, sumRange_succ, ih]
    omega

/-- A constant factor comes out of a sum. -/
theorem sumRange_const_mul (n : Nat) (c : Nat) (f : Nat → Nat) :
    sumRange n (fun i => c * f i) = c * sumRange n f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumRange_succ, sumRange_succ, ih, Nat.mul_add]

/-- The sum of a constant. -/
theorem sumRange_const (n c : Nat) : sumRange n (fun _ => c) = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumRange_succ, ih, Nat.succ_mul]

/-- **Splitting a range.**  A sum over `[0, a+b)` splits into the part below `a`
and the shifted part above it. -/
theorem sumRange_split (a b : Nat) (f : Nat → Nat) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun i => f (a + i)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hidx : a + (b + 1) = (a + b) + 1 := by omega
    rw [hidx, sumRange_succ, ih, sumRange_succ]
    omega

/-- Splitting a range in half, the form used by the doubling induction. -/
theorem sumRange_two_mul (n : Nat) (f : Nat → Nat) :
    sumRange (2 * n) f = sumRange n f + sumRange n (fun i => f (n + i)) := by
  have h : 2 * n = n + n := by omega
  rw [h, sumRange_split]

/-- Every summand is dominated by the whole sum. -/
theorem le_sumRange {n : Nat} (f : Nat → Nat) {i : Nat} (hi : i < n) :
    f i ≤ sumRange n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumRange_succ]
    by_cases h : i < n
    · have := ih h; omega
    · have hin : i = n := by omega
      subst hin
      omega

/-- A sum of nonnegative terms is monotone in the length of the range. -/
theorem sumRange_mono_length {a b : Nat} (f : Nat → Nat) (h : a ≤ b) :
    sumRange a f ≤ sumRange b f := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl 0
  | succ b ih =>
    rw [sumRange_succ]
    by_cases hab : a ≤ b
    · have := ih hab; omega
    · have : a = b + 1 := by omega
      subst this
      rw [sumRange_succ]
      omega

/-! ## Counting with indicators -/

/-- `countRange n p` counts the indices below `n` satisfying the Boolean
predicate `p`. -/
def countRange (n : Nat) (p : Nat → Bool) : Nat :=
  sumRange n (fun i => if p i then 1 else 0)

/-- The empty count. -/
@[simp] theorem countRange_zero (p : Nat → Bool) : countRange 0 p = 0 := rfl

/-- Peeling off the last index. -/
theorem countRange_succ (n : Nat) (p : Nat → Bool) :
    countRange (n + 1) p = countRange n p + (if p n then 1 else 0) := rfl

/-- **Counting against a weight.**  If every counted index carries weight at
least `w`, then `w` times the count is at most the total weight. -/
theorem mul_countRange_le {n w : Nat} {p : Nat → Bool} {f : Nat → Nat}
    (h : ∀ i, i < n → p i = true → w ≤ f i) :
    w * countRange n p ≤ sumRange n f := by
  rw [countRange, ← sumRange_const_mul]
  refine sumRange_le (fun i hi => ?_)
  by_cases hp : p i
  · rw [if_pos hp, Nat.mul_one]
    exact h i hi hp
  · rw [if_neg hp, Nat.mul_zero]
    exact Nat.zero_le _

/-- A count never exceeds the length of the range. -/
theorem countRange_le (n : Nat) (p : Nat → Bool) : countRange n p ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [countRange_succ]
    by_cases hp : p n
    · rw [if_pos hp]; omega
    · rw [if_neg hp]; omega

end Sum
end Collatz
