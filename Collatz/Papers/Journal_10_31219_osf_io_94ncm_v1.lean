import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jochen Kiemes, "Bit-Position Dynamics and a Lower Bound for Collatz Cycle Length", 2025.

Title: Bit-Position Dynamics and a Lower Bound for Collatz Cycle Length

Abstract (from harvested metadata, truncated):
We present a novel reformulation of the Collatz conjecture by leveraging the binary structure of positive integers, focusing on the sequence of odd terms. Through an analysis of leading and trailing bit-position dynamics, we derive a substantial lower bound of at least 17,026,679,261steps for any hypothetical non-trivial cycle, offering new insights into its structural constraints.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/94ncm_v1
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_94ncm_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jochen Kiemes, \"Bit-Position Dynamics and a Lower Bound for Collatz Cycle Length\", DOI:10.31219/osf.io/94ncm_v1 [2025]."

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

end Collatz.Papers.Journal_10_31219_osf_io_94ncm_v1
