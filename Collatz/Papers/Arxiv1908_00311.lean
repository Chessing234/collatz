import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Roger Zarnowski, "A Refinement of the $3x+1$ Problem", arXiv:1908.00311 [2019].

Title: A Refinement of the $3x+1$ Problem

Abstract (from OpenAlex metadata, truncated):
We reformulate the $3x+1$ conjecture by restricting attention to numbers congruent to $2$ (mod $3$). This leads to an equivalent conjecture for positive integers that reveals new aspects of the dynamics of the $3x+1$ problem. Advantages include a governing function with particularly simple mapping properties in terms of partitions of the set of integers. We use the refined conjecture to obtain a new characterization of $3x+1$ trajectories that shows a special role played by numbers congruent to $2$ or $8$ (mod $9$). We also present an accelerated iteration whose long-term behavior involves only those numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1908.00311
-/

namespace Collatz.Papers.Arxiv1908_00311

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Roger Zarnowski, \"A Refinement of the $3x+1$ Problem\", arXiv:1908.00311 [2019]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1908_00311
