import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Haruto Ariyoshi, "A Local Three-Period Structure and Diophantine Constraints in the Inverse Collatz Graph", 2026.

Title: A Local Three-Period Structure and Diophantine Constraints in the Inverse Collatz Graph

Abstract (from harvested metadata, truncated):
We study the inverse graph associated with the accelerated Collatz map on positive odd integers. We establish a local three-periodicity property for the admissible inverse exponents: for a fixed parent odd integer, the residue classes modulo 3 of its successive inverse children repeat with period three, although the phase depends on the parent residue class. We then derive the exact recurrence around a hypothetical odd cycle and obtain a corresponding global exponential Diophantine equation. Several necessary congruence and growth conditions for a nontrivial positive cycle are also established. These results provide a rigorous structural framework for studying possible cycles in the inverse...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22655873
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22655873

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Haruto Ariyoshi, \"A Local Three-Period Structure and Diophantine Constraints in the Inverse Collatz Graph\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22655873 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22655873
