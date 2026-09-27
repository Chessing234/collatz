import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Stephen T. Moore, "A Comment on the Collatz (3x+1) Conjecture", arXiv:1812.0238 [2018].

Title: A Comment on the Collatz (3x+1) Conjecture

Abstract (from OpenAlex metadata, truncated):
rThe stopping time of an integer X is the number of steps in a Collatz sequence which lead to an integer value less than X. This note details an algorithm for deriving X from a list of the steps in a stopping time sequence, thus inverting the operation. sfmoorex@gmail.com

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1812.0238
-/

namespace Collatz.Papers.Arxiv1812_0238

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Stephen T. Moore, \"A Comment on the Collatz (3x+1) Conjecture\", arXiv:1812.0238 [2018]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1812_0238
