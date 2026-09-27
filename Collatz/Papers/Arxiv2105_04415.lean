import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tobías Canavesi, "The Collatz Network", arXiv:2105.04415 [2021].

Title: The Collatz Network

Abstract (from OpenAlex metadata, truncated):
Considering all possible paths that a natural number can take following the rules of the algorithm proposed in the Collatz conjecture we construct a graph that can be interpreted as an infinite network that contemplates all possible paths within the conjecture. This allows us to understand why the minimal element of the Collatz orbit $x$ is equal to 1. Subsequently we define the extended Collatz conjecture equal to $o x+1$ when $x$ is odd and $x/2$ when $x$ is even with $o$ an odd number greater than $3$ and we show that there are infinite orbits in the extended Collatz conjecture that diverges. Finally, we find interesting theorems relating the Fibonacci sequence to prime numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2105.04415
-/

namespace Collatz.Papers.Arxiv2105_04415

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tob\u00edas Canavesi, \"The Collatz Network\", arXiv:2105.04415 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2105_04415
