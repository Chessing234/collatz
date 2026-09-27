import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Srdjan Kadić and S. Tomovic, "Computer-Based Validation of 3n+1 Hypothesis for Numbers 3n−1", 2019.

Title: Computer-Based Validation of 3n+1 Hypothesis for Numbers 3n−1

Abstract (from harvested metadata, truncated):
The formulation of the 3 n -1 problem is simple but no one has found the solution yet.This paper transforms the original problem into its equivalent so that it becomes more suitable for computer validation.A new algorithm is proposed and implemented.The hypothesis is tested and proven to be valid for numbers 3 n -1, conclusive with number 3 32768 -1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17559/tv-20161108221649
-/

namespace Collatz.Papers.Journal_10_17559_tv_20161108221649

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Srdjan Kadić and S. Tomovic, \"Computer-Based Validation of 3n+1 Hypothesis for Numbers 3n−1\", Tehnicki vjesnik - Technical Gazette, DOI:10.17559/tv-20161108221649 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_17559_tv_20161108221649
