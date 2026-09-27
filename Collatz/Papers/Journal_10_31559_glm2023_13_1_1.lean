import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aiman Eid Al‐Rawajfeh, "A Conjecture from Collatz Conjecture: Elevation by Folding", 2023.

Title: A Conjecture from Collatz Conjecture: Elevation by Folding

Abstract (from harvested metadata, truncated):
The Collatz Conjecture proposed in 1937 by German mathematician Lothar Collatz remains unsolved. It states that: let ℕ be the set of all positive integers and n ϵ ℕ, then: any positive integer n will collapse to 1 by applying the rules of the conjecture: 3n+1 (for odd numbers) and n/2 (for even numbers). In this work, a new conjecture was stated from Collatz conjecture. Percentage crystallinity was defined and a unique solution of the elevation (reverse) of the cyclone part and the whole stem was suggested. The % Crystallinity of the 512-line on the stem is 100% while it is 68% for the 184-line. The only number, f(n) = 112n, resulting from multiplication of prime numbers, that satisfies the elevation of Collatz cyclone is 112 (i.e., n = 1), and for the elevation of the stem, the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31559/glm2023.13.1.1
-/

namespace Collatz.Papers.Journal_10_31559_glm2023_13_1_1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aiman Eid Al‐Rawajfeh, \"A Conjecture from Collatz Conjecture: Elevation by Folding\", General Letters in Mathematics, DOI:10.31559/glm2023.13.1.1 [2023]."

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

end Collatz.Papers.Journal_10_31559_glm2023_13_1_1
