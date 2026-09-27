import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lizhi Du, "Method Study on the 3x+1 Problem", arXiv:1205.0845 [2012].

Title: Method Study on the 3x+1 Problem

Abstract (from OpenAlex metadata, truncated):
The 3x+1 problem is one of the most classical problems in computer science, related to many fields. As it is thought by scientists a highly hard problem, resolving it successfully not only can improve the research in many relating fields, but also be meaningful to the method study. By deep analyzing the 3x+1 calculation process with the input positive integer becoming greater, we find a useful way for solving this problem with high probability. By making use of the greater calculating ability of great computers and the internet, our way is a valid and powerful way for utterly solving the 3x+1 problem. This way can be expressed in three points: 1) If we can find a positive integer N, for any positive integer less than 2N, the times of dividing 2 out of its stopping time is less than or equal to N, then the 3x+1 conjecture is true; 2) This N may be big, so the calculation may be too big. O

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1205.0845
-/

namespace Collatz.Papers.Arxiv1205_0845

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lizhi Du, \"Method Study on the 3x+1 Problem\", arXiv:1205.0845 [2012]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1205_0845
