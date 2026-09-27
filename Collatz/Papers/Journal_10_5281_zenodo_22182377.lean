import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael M. Ross, "michaelmross/Collatz: Accelerated Collatz Map", 2026.

Title: michaelmross/Collatz: Accelerated Collatz Map

Abstract (from harvested metadata, truncated):
Code supporting Spike Structures and 2-adic Transition Laws in the Accelerated Collatz Map and Loop Structure of Collatz-Type Functions 3x+n: A Conjugacy Theorem and Powers of Three (Ross, M. M., 2026).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22182377
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22182377

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael M. Ross, \"michaelmross/Collatz: Accelerated Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22182377 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22182377
