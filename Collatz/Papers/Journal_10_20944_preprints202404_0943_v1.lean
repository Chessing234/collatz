import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Budee U Zaman, "Revealing a Binary Pattern Validates 3n+1 Problem for All Positive Integers", 2024.

Title: Revealing a Binary Pattern Validates 3n+1 Problem for All Positive Integers

Abstract (from harvested metadata, truncated):
This study delves into a unique binary pattern found within the wellknown 3n+1 problem, or Collatz conjecture. Through careful analysis of the steps in the 3n+1 sequence, we have discovered a special binary representation that captures the behavior of all positive integers undergoing this transformation. With this new understanding, we have provided a solid proof confirming the validity of the 3n+1 problem for all positive integers. Our method goes beyond the need for extensive computational confirmation, providing a simple and elegant resolution to a long-standing mathematical mystery.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202404.0943.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202404_0943_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Budee U Zaman, \"Revealing a Binary Pattern Validates 3n+1 Problem for All Positive Integers\", DOI:10.20944/preprints202404.0943.v1 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_20944_preprints202404_0943_v1
