import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maarten J. Wensink, "The 3n+1 problem: a partition of interest", arXiv:1908.01509 [2019].

Title: The 3n+1 problem: a partition of interest

Abstract (from OpenAlex metadata, truncated):
A mapping conjugate to the Collatz mapping seems to imply that $\N=\{1,2,3,\ldots\}$ is partitioned in a trivial loop $\{1\}$ and `strings' that are ordered subsets of $\{\N \setminus 1\}$ that run from an element of $\{2+3\0\}$ to an element of $\{3+4\0\}$ ($\0=0 \cup \N$). In particular, this means that all trajectories except for the trivial loop go through an element of $\{3+4\0\}$ ($\{5+8\0\}$ for the original mapping). I give reasons for this conjecture. Next, I note that the 3n+1 numbers and the 3n+3 numbers are the only numbers from the generalization $3n+p, p \in \{\ldots,-3,-1,1,3,\ldots\}$ for which such a partition seems to exist. Suspiciously, these are also the only members for which the conjecture (reduction to the trivial loop) seems to hold.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1908.01509
-/

namespace Collatz.Papers.Arxiv1908_01509

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maarten J. Wensink, \"The 3n+1 problem: a partition of interest\", arXiv:1908.01509 [2019]."

/-- Recorded claim shell (generalization); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1908_01509
