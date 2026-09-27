import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hans-Dieter A. Hiep, "Can the Collatz conjecture be proven, or not?", 2023.

Title: Can the Collatz conjecture be proven, or not?

Abstract (from harvested metadata, truncated):
Can the Collatz conjecture be proven, or not? Download the PDF version of this article. collatz.pdf 236 KB In 1937, shortly after the mathematician Lothar Collatz obtained his doctorate, he wrote down a problem in his notebook that later became known as Collatz' problem or the \(3x+1)\-problem . The problem is remarkable since it is easy to state, but for more than eighty years no solution had been found.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.59350/0kcex-08q27
-/

namespace Collatz.Papers.Journal_10_59350_0kcex_08q27

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hans-Dieter A. Hiep, \"Can the Collatz conjecture be proven, or not?\", DOI:10.59350/0kcex-08q27 [2023]."

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

end Collatz.Papers.Journal_10_59350_0kcex_08q27
