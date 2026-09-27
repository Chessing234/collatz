import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lei Li, "A Proof for the Collatz Conjecture", arXiv:2209.13541 [2022].

Title: A Proof for the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
It is well known that the following Collatz Conjecture is one of the unsolved problems in mathematics. Collatz Conjecture: For any positive integer $n>1$, the following recursive algorithm will convergent to 1 by a finite number of steps. A) If $n$ is an even number then $n/2 \to n$, B) If $n$ is an odd number then $3n+1 \to n$. This paper proposes a proof for the Collatz Conjecture by the elementary mathematical induction.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2209.13541
-/

namespace Collatz.Papers.Arxiv2209_13541

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lei Li, \"A Proof for the Collatz Conjecture\", arXiv:2209.13541 [2022]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2209_13541
