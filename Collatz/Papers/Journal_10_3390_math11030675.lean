import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kamal Barghout et al., "Statistical Analysis of Descending Open Cycles of Collatz Function", 2023.

Title: Statistical Analysis of Descending Open Cycles of Collatz Function

Abstract (from harvested metadata, truncated):
Collatz dynamic systems present a statistical space that can be studied rigorously. In a previous study, the author presented Collatz space in a unique dynamic numerical mode by tabulating a sequential correlation pattern of division by 2 of Collatz function’s even numbers until the numbers became odd with a consecutive occurrence, following an attribute of a 50:50 probability of division by 2 once (ascending behavior) as opposed to division by 2 more than once (descending behavior). In this paper, we describe the path of the Collatz function as sequences comprised of groups of the function’s iterates (open cycles) that end up with the first odd integer that is less than the starting odd integer. The descending behavior of the open cycles is attributed to a deterministic factor as...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/math11030675
-/

namespace Collatz.Papers.Journal_10_3390_math11030675

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kamal Barghout et al., \"Statistical Analysis of Descending Open Cycles of Collatz Function\", Mathematics, DOI:10.3390/math11030675 [2023]."

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

end Collatz.Papers.Journal_10_3390_math11030675
