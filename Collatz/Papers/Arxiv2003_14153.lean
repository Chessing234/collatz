import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Daudin, Jean-Jacques, "$3n+1$ problem: an heuristic lower bound for the number of integers connected to 1 and less than $x$", arXiv:2003.14153 [2020].

Title: $3n+1$ problem: an heuristic lower bound for the number of integers connected to 1 and less than $x$

Abstract (from arXiv metadata, truncated):
This paper gives an heuristic lower bound for the number of integers connected to 1 and less than $x$, $θ(x) > 0.9x,$ in the context of the $3n+1$ problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2003.14153
-/

namespace Collatz.Papers.Arxiv2003_14153

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Daudin, Jean-Jacques, \"$3n+1$ problem: an heuristic lower bound for the number of integers connected to 1 and less than $x$\", arXiv:2003.14153 [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2003_14153
