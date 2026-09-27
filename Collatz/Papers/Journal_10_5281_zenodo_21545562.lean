import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ali Alhawarat, "The Odd Node and Loop Hypothesis: A Structural Interpretation of the Collatz Dynamics", 2026.

Title: The Odd Node and Loop Hypothesis: A Structural Interpretation of the Collatz Dynamics

Abstract (from harvested metadata, truncated):
This work proposes a structural interpretation of the Collatz graph centered on the unique role of the integer 1. Rather than treating 1 merely as the endpoint of the known positive cycle, the paper introduces the concept of the Odd Node, interpreted as the unique structural junction connecting the binary (even) backbone and the ternary (odd) hierarchy. The framework introduces the First Door Principle, the Single-Node Principle, the Universal Door Conjecture, and the Maze Door Principle as structural interpretations of the observed dynamics. A numerical verification over a large finite domain found no evidence of an alternative positive Odd Node or an independent positive cycle. The work is...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21545562
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21545562

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ali Alhawarat, \"The Odd Node and Loop Hypothesis: A Structural Interpretation of the Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21545562 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21545562
