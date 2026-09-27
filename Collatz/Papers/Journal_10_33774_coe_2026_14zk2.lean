import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kevin Nwanozie, "Affine self similarities and the non existence of non trivia collatz cycles ;a critical analysis", 2026.

Title: Affine self similarities and the non existence of non trivia collatz cycles ;a critical analysis

Abstract (from harvested metadata, truncated):
We provide a critical analysis.if a previous proof attempt and reveal a signifiy flaw that undermines the proof attempt.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2026-14zk2
-/

namespace Collatz.Papers.Journal_10_33774_coe_2026_14zk2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kevin Nwanozie, \"Affine self similarities and the non existence of non trivia collatz cycles ;a critical analysis\", DOI:10.33774/coe-2026-14zk2 [2026]."

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

end Collatz.Papers.Journal_10_33774_coe_2026_14zk2
