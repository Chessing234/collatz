import Collatz.Structure.AccCycle
import Collatz.Structure.Density
import Collatz.Core.Sum

/-!
# Summing over a cycle

Every constraint so far looked at cycle points one at a time.  This file adds
one more, obtained by summing the defining relation around the whole loop.

For each step, `2 · T(x) = x` when `x` is even and `2 · T(x) = x + (2x + 1)`
when `x` is odd.  Summing over a full period, the left side telescopes — the
orbit returns, so `Σ T(x_i) = Σ x_i` — and what is left is

**`S = 2 · S_odd + a`**

where `S` is the sum of all cycle points, `S_odd` the sum of the odd ones, and
`a` the number of odd steps.  Equivalently `S_even = S_odd + a`: *the even points
of a cycle outweigh the odd points by exactly the number of odd steps.*

It is a genuine identity rather than an inequality, and it is independent of the
size and length bounds, so it constrains a hypothetical cycle from a direction
none of the earlier lemmas touch.
-/

namespace Collatz
namespace CycleSum

open Reach AccCycle _root_.Collatz.Sum

/-! ## Shifting a finite sum -/

/-- Shifting the index of a finite sum trades the first term for the last. -/
theorem sumRange_shift (L : Nat) (f : Nat → Nat) :
    sumRange L (fun i => f (i + 1)) + f 0 = sumRange L f + f L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sumRange_succ, sumRange_succ]
    omega

/-- On a cycle the shifted sum equals the original, because the orbit returns. -/
theorem sumRange_shift_of_cycle {n L : Nat} (h : acceleratedOrbit L n = n) :
    sumRange L (fun i => acceleratedOrbit (i + 1) n) =
      sumRange L (fun i => acceleratedOrbit i n) := by
  have hs := sumRange_shift L (fun i => acceleratedOrbit i n)
  have h0 : acceleratedOrbit 0 n = n := rfl
  rw [h0, h] at hs
  omega

/-! ## The odd-step count as a sum -/

/-- The odd-step count is the sum of the parities along the orbit. -/
theorem oddCount_eq_sumRange (n L : Nat) :
    oddCount n L = sumRange L (fun i => acceleratedOrbit i n % 2) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Density.oddCount_succ_last, ih, sumRange_succ]

/-! ## The cycle sums -/

/-- The sum of all points of a cycle of length `L` through `n`. -/
def cycleSum (n L : Nat) : Nat := sumRange L (fun i => acceleratedOrbit i n)

/-- The sum of the odd points of the cycle. -/
def cycleOddSum (n L : Nat) : Nat :=
  sumRange L (fun i => if acceleratedOrbit i n % 2 = 1 then acceleratedOrbit i n else 0)

/-- One step, rearranged so that summation is immediate. -/
theorem two_mul_step (x : Nat) :
    2 * acceleratedStep x = x + (if x % 2 = 1 then 2 * x + 1 else 0) := by
  rcases Arith.mod_two_eq_zero_or_one x with he | ho
  · rw [acceleratedStep, if_pos he, if_neg (by omega)]
    omega
  · rw [acceleratedStep, if_neg (by omega), if_pos ho]
    omega

/-- **The cycle-sum identity.**  `S = 2 · S_odd + a`. -/
theorem cycleSum_eq {n L : Nat} (h : acceleratedOrbit L n = n) :
    cycleSum n L = 2 * cycleOddSum n L + oddCount n L := by
  -- expand `2 · T(x_i)` termwise
  have hterm : ∀ i : Nat,
      2 * acceleratedOrbit (i + 1) n
        = acceleratedOrbit i n
          + (if acceleratedOrbit i n % 2 = 1 then 2 * acceleratedOrbit i n + 1 else 0) := by
    intro i
    rw [acceleratedOrbit_succ_step]
    exact two_mul_step _
  -- sum both sides
  have hsum : sumRange L (fun i => 2 * acceleratedOrbit (i + 1) n)
      = sumRange L (fun i => acceleratedOrbit i n
          + (if acceleratedOrbit i n % 2 = 1 then 2 * acceleratedOrbit i n + 1 else 0)) :=
    sumRange_congr (fun i _ => hterm i)
  rw [sumRange_const_mul, sumRange_add] at hsum
  rw [sumRange_shift_of_cycle h] at hsum
  -- split the conditional sum into its two pieces
  have hsplit : sumRange L
      (fun i => if acceleratedOrbit i n % 2 = 1 then 2 * acceleratedOrbit i n + 1 else 0)
      = 2 * cycleOddSum n L + oddCount n L := by
    rw [oddCount_eq_sumRange, cycleOddSum, ← sumRange_const_mul, ← sumRange_add]
    refine sumRange_congr (fun i _ => ?_)
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit i n) with he | ho
    · simp [he]
    · simp [ho]
  rw [hsplit] at hsum
  rw [cycleSum]
  omega

/-- **The even points outweigh the odd ones by exactly the odd-step count.**
Restated: `S_even = S_odd + a`. -/
theorem cycleEvenSum_eq {n L : Nat} (h : acceleratedOrbit L n = n) :
    cycleSum n L = cycleOddSum n L + (cycleOddSum n L + oddCount n L) := by
  have := cycleSum_eq h
  omega

/-- The odd points never make up more than half the total. -/
theorem two_mul_cycleOddSum_le {n L : Nat} (h : acceleratedOrbit L n = n) :
    2 * cycleOddSum n L ≤ cycleSum n L := by
  have := cycleSum_eq h
  omega

/-- On a nontrivial cycle at least one point is odd, so the odd sum is
positive. -/
theorem cycleOddSum_pos {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    0 < cycleOddSum n L := by
  have hcount : 0 < oddCount n L := oddCount_pos_of_accCycle hn h
  -- some index in range carries an odd value
  have hex : ∃ i : Nat, i < L ∧ acceleratedOrbit i n % 2 = 1 := by
    by_cases hc : ∃ i : Nat, i < L ∧ acceleratedOrbit i n % 2 = 1
    · exact hc
    · exfalso
      have hall : ∀ i : Nat, i < L → acceleratedOrbit i n % 2 = 0 := by
        intro i hi
        rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit i n) with he | ho
        · exact he
        · exact absurd ⟨i, hi, ho⟩ hc
      rw [oddCount_eq_sumRange] at hcount
      have hcongr : sumRange L (fun i => acceleratedOrbit i n % 2)
          = sumRange L (fun _ => 0) := sumRange_congr (fun i hi => hall i hi)
      rw [hcongr, sumRange_const] at hcount
      omega
  obtain ⟨i, hi, hodd⟩ := hex
  have hle := le_sumRange (n := L)
    (fun j => if acceleratedOrbit j n % 2 = 1 then acceleratedOrbit j n else 0) hi
  rw [if_pos hodd] at hle
  have hpos : 0 < acceleratedOrbit i n := acceleratedOrbit_positive hn i
  have heq : cycleOddSum n L
      = sumRange L (fun j => if acceleratedOrbit j n % 2 = 1 then acceleratedOrbit j n else 0) :=
    rfl
  omega

end CycleSum
end Collatz
