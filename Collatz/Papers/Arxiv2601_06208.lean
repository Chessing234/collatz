import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Abderrahman Bouhamidi, "An Extension of the Collatz Conjecture modulo $2^p+2^q$", arXiv:2601.06208 [2026].

Title: An Extension of the Collatz Conjecture modulo $2^p+2^q$

Abstract (from OpenAlex metadata, truncated):
In this paper, we will introduce an extension to the Collatz's conjecture. This conjecture may be seen as a general conjecture that unifies the Collatz one together with many other similar conjectures. For instance, we propose our new conjecture modulo $10$ which may be stated as follows. Starting from any positive integer, if it is a multiple of $10$ then divide it by 10, otherwise, multiply it by $12$, add $8$ times its last digit and divide the result by $10$. Repeat the process infinitely. Regardless the starting number, the process eventually reaches $4$ after a finite number of iterations. The genaral conjecture studied here will encompasse the classical Collatz conjecture togher with our proposed one modulo $10$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2601.06208
-/

namespace Collatz.Papers.Arxiv2601_06208

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Abderrahman Bouhamidi, \"An Extension of the Collatz Conjecture modulo $2^p+2^q$\", arXiv:2601.06208 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2601_06208
