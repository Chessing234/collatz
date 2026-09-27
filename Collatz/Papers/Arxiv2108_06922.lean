import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ashish Tiwari, "A Conjecture Equivalent to the Collatz Conjecture", arXiv:2108.06922 [2021].

Title: A Conjecture Equivalent to the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
We present a formulation of the Collatz conjecture that is potentially more amenable to modeling and analysis by automated termination checking tools.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2108.06922
-/

namespace Collatz.Papers.Arxiv2108_06922

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ashish Tiwari, \"A Conjecture Equivalent to the Collatz Conjecture\", arXiv:2108.06922 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2108_06922
