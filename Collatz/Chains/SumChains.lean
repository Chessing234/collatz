import Collatz.Chains.Sharp
import Collatz.Structure.CycleSum

/-!
# Chains 81–85: the cycle-sum identity

Summing the step relation around a cycle gives

`S = 2 · S_odd + a`,  equivalently  `S_even = S_odd + a`

(`CycleSum.cycleSum_eq`).  It is an *identity*, not an inequality, and it is
independent of the size and length bounds — so it constrains a hypothetical
cycle from a direction none of the other lemmas touch.

The chains below convert it into targets.  Each hypothesis contradicts the
identity, so proving any of them closes the cycle half.
-/

namespace Collatz
namespace Chains

open Reach Strategy AccCycle AccDivergence CycleSum

/-- Hypothesis: some cycle has no odd points. -/
def H81_noOddPoints : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleOddSum n L = 0

/-- **Chain 81.**  Every cycle has an odd point, so its odd sum is positive. -/
theorem chain81 (h1 : H14a_noAccDivergence) (h2 : H81_noOddPoints) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hzero := h2 n L hn hc
  have hpos := cycleOddSum_pos hn hc
  omega

/-- Hypothesis: the odd points of a cycle carry more than half its total. -/
def H82_oddHeavy : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleSum n L < 2 * cycleOddSum n L

/-- **Chain 82.**  The identity forces the odd points to carry at most half. -/
theorem chain82 (h1 : H14a_noAccDivergence) (h2 : H82_oddHeavy) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have hheavy := h2 n L hn hc
  have hle := two_mul_cycleOddSum_le hc.2
  omega

/-- Hypothesis: the sum identity fails by at least the odd-step count. -/
def H83_sumMismatch : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L →
    cycleSum n L ≠ 2 * cycleOddSum n L + oddCount n L

/-- **Chain 83.**  The identity always holds, so this closes the cycle half. -/
theorem chain83 (h1 : H14a_noAccDivergence) (h2 : H83_sumMismatch) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  exact absurd (cycleSum_eq hc.2) (h2 n L hn hc)

/-- Hypothesis: every cycle's total is smaller than its odd-step count. -/
def H84_tinySum : Prop :=
  ∀ n L : Nat, 0 < n → AccIsCycleOf n L → cycleSum n L < oddCount n L

/-- **Chain 84.**  The identity makes the total at least the odd-step count. -/
theorem chain84 (h1 : H14a_noAccDivergence) (h2 : H84_tinySum) :
    CollatzConjecture := by
  refine collatz_of_cycles_reach h1 (fun n L hn hc => ?_)
  have htiny := h2 n L hn hc
  have hid := cycleSum_eq hc.2
  omega

/-- **Chain 85.**  The sum-identity targets, collected.  Each closes the cycle
half on its own, given no divergence. -/
theorem chain85 (h1 : H14a_noAccDivergence) :
    (H81_noOddPoints → CollatzConjecture) ∧
    (H82_oddHeavy → CollatzConjecture) ∧
    (H83_sumMismatch → CollatzConjecture) ∧
    (H84_tinySum → CollatzConjecture) :=
  ⟨chain81 h1, chain82 h1, chain83 h1, chain84 h1⟩

end Chains
end Collatz
