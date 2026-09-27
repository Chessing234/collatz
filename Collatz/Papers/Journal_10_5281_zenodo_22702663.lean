import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Virgil Lee Gattenby, "Snowman Conjecture Mathic: local continuity closure and verified Collatz address folds", 2026.

Title: Snowman Conjecture Mathic: local continuity closure and verified Collatz address folds

Abstract (from harvested metadata, truncated):
Author: Virgil Lee Gattenby. Collatz conjecture research package with the locked Snowman Mathic score, Lean 4 fold identities, and local continuity verification. Benchmark: 100,000 odd source addresses, four archived fixtures, and a corrupted-packet rejection test. Local closure covers address reconstruction, fold identities, and typed continuity. Universal finite Collatz orbit termination is not established.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22702663
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22702663

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Virgil Lee Gattenby, \"Snowman Conjecture Mathic: local continuity closure and verified Collatz address folds\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22702663 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22702663
