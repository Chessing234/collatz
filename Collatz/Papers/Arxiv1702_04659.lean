import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Esse Koudam, "Canonical decomposition in $\mathbb{r}_+^*$ of a convergent natural number by the collatz iterations", arXiv:1702.04659 [2017].

Title: Canonical decomposition in $\mathbb{r}_+^*$ of a convergent natural number by the collatz iterations

Abstract (from OpenAlex metadata, truncated):
The Collatz variations pattern seems not to have any recurrence relation between numbers. But knowing that there is at least a natural number that converges after several iterations we construct a function $f_{X,Y}$ that is equal to the value of convergence for all convergent sequences. A canonical decomposition can be expressed for such numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1702.04659
-/

namespace Collatz.Papers.Arxiv1702_04659

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Esse Koudam, \"Canonical decomposition in $\\mathbb{r}_+^*$ of a convergent natural number by the collatz iterations\", arXiv:1702.04659 [2017]."

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

end Collatz.Papers.Arxiv1702_04659
