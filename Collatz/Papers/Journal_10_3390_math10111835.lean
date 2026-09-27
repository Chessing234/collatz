import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aberkane, Idriss J., "Collatz Attractors Are Space-Filling", 2022.

Title: Collatz Attractors Are Space-Filling

Abstract (from harvested metadata, truncated):
The algebraic topology of Collatz attractors (or “Collatz Feathers”) remains very poorly understood. In particular, when pushed to infinity, is their set of branches discrete or continuous? Here, we introduce a fundamental theorem proving that the latter is true. For any odd x, we first define Axn as the set of all odd numbers with Syr(x) in their Collatz orbit and up to n more digits than x in base 2. We then prove limn→∞|Axn|2n+c≥1 with c&gt;−4 for all x and, in particular, c=0 for x=1, which is a result strictly stronger than that of Tao 2019.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/math10111835
-/

namespace Collatz.Papers.Journal_10_3390_math10111835

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aberkane, Idriss J., \"Collatz Attractors Are Space-Filling\", Mathematics, DOI:10.3390/math10111835 [2022]."

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

end Collatz.Papers.Journal_10_3390_math10111835
