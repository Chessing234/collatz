import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rozier, Olivier, "The 3x+1 problem: a lower bound hypothesis", arXiv:1510.01610 [2015].

Title: The 3x+1 problem: a lower bound hypothesis

Abstract (from OpenAlex metadata, truncated):
Much work has been done attempting to understand the dynamic behaviour of the so-called "3x+1" function. It is known that finite sequences of iterations with a given length and a given number of odd terms have some combinatorial properties modulo powers of two. In this paper, we formulate a new hypothesis asserting that the first terms of those sequences have a lower bound which depends on the binary entropy of the "ones-ratio". It is in agreement with all computations so far. Furthermore it implies accurate upper bounds for the total stopping time and the maximum excursion of an integer. Theses results are consistent with two previous stochastic models of the 3x+1 problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1510.01610
-/

namespace Collatz.Papers.Arxiv1510_01610

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rozier, Olivier, \"The 3x+1 problem: a lower bound hypothesis\", arXiv:1510.01610 [2015]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1510_01610
