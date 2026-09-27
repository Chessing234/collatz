import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kevin Knight, "A Small Collatz Rule without the Plus One", 2026.

Title: A Small Collatz Rule without the Plus One

Abstract (from harvested metadata, truncated):
The Collatz rule is one of the earliest examples of a simple, deterministic system that produces chaotic behavior. The rule takes any odd positive integer n to 3n+1 and any even positive integer n to n/2. Iterating this rule yields complex sequences whose dynamics are poorly understood; for example, it is unknown whether all such sequences reach 1 (the Collatz conjecture). It is reasonable to suspect that this complexity derives from the interplay of multiplication (3n) and addition (+1). However, in 2002, Monks was able to drop the +1 by constructing a 1 021 020-condition rule that simulates the Collatz rule using only multiplication. Monks’s rule greatly simplifies the Collatz dynamics but...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.25088/complexsystems.35.1.1
-/

namespace Collatz.Papers.Journal_10_25088_complexsystems_35_1_1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kevin Knight, \"A Small Collatz Rule without the Plus One\", Complex Systems, DOI:10.25088/complexsystems.35.1.1 [2026]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_25088_complexsystems_35_1_1
