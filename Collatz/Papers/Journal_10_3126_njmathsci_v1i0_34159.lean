import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Subedi, Bishnu Hari and Singh, Ajaya, "3n+1 Problem and its Dynamics", 2020.

Title: 3n+1 Problem and its Dynamics

Abstract (from harvested metadata, truncated):
The subject of this paper is the well-known 3n + 1 problem of elementary number theory. This problem concerns with the behaviour of the iteration of a function which takes odd integers n to 3n + 1, and even integers n to n/2. There is a famous Collatz conjecture associated to this problem which asserts that, starting from any positive integer n, repeated iteration of the function eventually produces the value. We briefly discuss some basic facts and results of 3n + 1 problem and Collatz conjecture. Basically, we more concentrate on the generalization of this problem and conjecture to holomorphic dynamics.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3126/njmathsci.v1i0.34159
-/

namespace Collatz.Papers.Journal_10_3126_njmathsci_v1i0_34159

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Subedi, Bishnu Hari and Singh, Ajaya, \"3n+1 Problem and its Dynamics\", Nepal Journal of Mathematical Sciences, DOI:10.3126/njmathsci.v1i0.34159 [2020]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_3126_njmathsci_v1i0_34159
