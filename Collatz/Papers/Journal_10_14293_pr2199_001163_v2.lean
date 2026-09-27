import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Javier Hernandez, "Looking for cycles in an alternative representation of the Collatz sequences", 2024.

Title: Looking for cycles in an alternative representation of the Collatz sequences

Abstract (from harvested metadata, truncated):
Would it be possible to define a procedure capable to find all the existing cycles within the Collatz sequences? In this article we address this question in two stages: in the first one, we propose an equivalent and reversible set of actions to represent any Hailstone sequence. In the second one, we show a condition which any loop satisfies within this new definition, ultimately revealing that the problem 3n + 1 generates just a single cycle for any value of n, being moreover, always reached.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.14293/pr2199.001163.v2
-/

namespace Collatz.Papers.Journal_10_14293_pr2199_001163_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Javier Hernandez, \"Looking for cycles in an alternative representation of the Collatz sequences\", DOI:10.14293/pr2199.001163.v2 [2024]."

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

end Collatz.Papers.Journal_10_14293_pr2199_001163_v2
