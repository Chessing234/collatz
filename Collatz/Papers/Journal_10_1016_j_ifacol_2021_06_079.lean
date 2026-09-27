import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for John Leventides and Costas Poulios, "An operator theoretic approach to the 3x + 1 dynamical system", 2021.

Title: An operator theoretic approach to the 3x + 1 dynamical system

Abstract (from harvested metadata, truncated):
The Collatz map T: N* → N* is defined on the positive integers by setting T(n) equal to 3n+1/2 when n is odd and n/2 when n is even. The Collatz conjecture (or 3x+1-problem) asserts that, for any positive integer n, the orbit of n produced by iterated applications of the map T finally reaches the number 1 in a finite number of steps. In this paper, we utilize techniques from Operator Theory in order to study the conjecture. This approach enables us to “lift” the problem from the set N* to spaces of functions defined on N*, that is to sequence spaces. Hence, the study of the trajectories of the Collatz map can be related to the study of properties of bounded linear operators defined on sequence spaces.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1016/j.ifacol.2021.06.079
-/

namespace Collatz.Papers.Journal_10_1016_j_ifacol_2021_06_079

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "John Leventides and Costas Poulios, \"An operator theoretic approach to the 3x + 1 dynamical system\", IFAC-PapersOnLine, DOI:10.1016/j.ifacol.2021.06.079 [2021]."

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

end Collatz.Papers.Journal_10_1016_j_ifacol_2021_06_079
