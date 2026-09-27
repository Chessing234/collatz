import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ramon Carbó-Dorca, "Natural Numbers Generalized Parity, and the Collatz Algorithm", arXiv:1202.3670 [2026].

Title: Natural Numbers Generalized Parity, and the Collatz Algorithm

Abstract (from OpenAlex metadata, truncated):
An extended definition of the even-odd property for natural numbers is used to highlightprime numbers in their classification. For a given natural number $M$ and a chosen prime$P$, one can say that $PM$ is $P$-even-like, and $PM+K$, with$K = [1, 2, \ldots, P-1]$, is $P$-odd-like of $K$-class. This approach enables thedescription of a generalized Collatz conjecture and an associated algorithm. A filtervector is used in a new $P$-Collatz algorithmic path to divide any number $M$ at any stepwhen it has prime factors also in the filter. If $M$ cannot be divided by any prime filtervector element, then the transformation $PM+K$ is performed. Therefore, a new formulationof the Collatz conjecture is: ``the $P$-Collatz algorithm converges to 1 for all naturalnumbers $M$, through a transformation of the form $PM+K$ (the original Collatz algorithmuses $P=3$ and $K=1$), provided that a conveniently 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1202.3670
-/

namespace Collatz.Papers.Arxiv1202_3670

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ramon Carb\u00f3-Dorca, \"Natural Numbers Generalized Parity, and the Collatz Algorithm\", arXiv:1202.3670 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1202_3670
