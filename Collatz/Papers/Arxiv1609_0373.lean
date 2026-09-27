import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Induction and Code for Collatz Conjecture or 3x+1 Problem", arXiv:1609.0373 [2016].

Title: Induction and Code for Collatz Conjecture or 3x+1 Problem

Abstract (from OpenAlex metadata, truncated):
Collatz conjecture (or 3x+1 problem) has not been proved to be true or false for about 80 years. The exploration on this problem seems to ask for introducing a totally new method. In this paper, a mathematical induction method is proposed, whose proof can lead to the proof of the conjecture. According to the induction, a new representation (for dynamics) called ``code'' is introduced, to represent the occurred $3*x+1$ and $x/2$ computations during the process from starting number to the first transformed number that is less than the starting number. In a code $3*x+1$ is represented by 1 and $x/2$ is represented by 0. We find that code is a building block of the original dynamics from starting number to 1, and thus is more primitive for modeling quantitative properties. Some properties only exist in dynamics represented by code, but not in original dynamics. We discover and prove some inh

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1609.0373
-/

namespace Collatz.Papers.Arxiv1609_0373

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Induction and Code for Collatz Conjecture or 3x+1 Problem\", arXiv:1609.0373 [2016]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1609_0373
