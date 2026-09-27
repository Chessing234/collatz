import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Spencer, Michael, "A Resolution of the Collatz Conjecture", 2025.

Title: A Resolution of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper presents a full resolution of the Collatz Conjecture. The approach combines both a local view of how individual numbers behave under the rules of the problem, and a global view of how all numbers together form a complete structure. From the local side, the paper shows how every number can be traced backwards in a predictable way using a new arithmetic method. This guarantees that each number comes from only one possible “parent,” creating a sort of family tree that never splits or loops. From the global side, the paper builds a recursive framework that spreads out to cover all possible numbers through consistent patterns. This means that no number is left out and everything fits. The core finding is that when both perspectives are put together, the Collatz process becomes fully...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17568084
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17568084

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Spencer, Michael, \"A Resolution of the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17568084 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17568084
