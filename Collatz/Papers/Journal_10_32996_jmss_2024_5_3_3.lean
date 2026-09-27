import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for AL-Shammary, Naif Mohammad, "Collatz Conjecture (3N+1) Solution", 2024.

Title: Collatz Conjecture (3N+1) Solution

Abstract (from harvested metadata, truncated):
Collatz Conjecture (3x+1) or in some literature as 3N+1 is a problem because it works in the way that if you take any positive number, if it is an odd number you multiply it by three (3) then add one (1). On the other hand, if it is an even number, you divide it by two (2). Eventually, all positive numbers decrease to one (1). One (1) is odd, so multiply it by three (3) is three (3) and add one (1) is four (4). Four (4) is even, so divide it by two (2) is two (2). Two (2) is also even, so divide it by two (2) is one (1) again. All positive numbers end up in the loop (4-2-1). This loop is like a numerical lock. Therefore, the solution of this problem will have to be a numerical key results to all positive numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.32996/jmss.2024.5.3.3
-/

namespace Collatz.Papers.Journal_10_32996_jmss_2024_5_3_3

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "AL-Shammary, Naif Mohammad, \"Collatz Conjecture (3N+1) Solution\", Journal of Mathematics and Statistics Studies, DOI:10.32996/jmss.2024.5.3.3 [2024]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_32996_jmss_2024_5_3_3
