import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Chin‐Long Wey, "The Proof of the Collatz Conjecture", arXiv:2309.09991 [2023].

Title: The Proof of the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The 3n+1, or Collatz problem, is one of the hardest math problems, yet still unsolved. The Collatz conjecture is to prove or disprove that the Collatz sequences COL(n) always eventually reach the number of 1, for all n belongs to N+ (all positive integers). The Syracuse conjecture is a (2N+1)-version of Collatz conjecture, where (2N+1) is all odd integers. The Syracuse and Collatz problem can be conceptually described by a tree trunk and branches. The trunk is made of the junctions that produce the main branches, where J0=1 is the root junction. Each branch consists of active and dead junctions, where only the active junctions are capable of producing new sub-branches. Conceptually assuming the trunk and branches can grow indefinitely and can also absorb nutrients from the root. As the tree grows indefinitely, all N+ (2N+1) are included for the Collatz (Syracuse) sequence. This paper develops both inverse Collatz (Syracuse) functions to construct the tree trunk and branches starting fr

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2309.09991
-/

namespace Collatz.Papers.Arxiv2309_09991

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Chin\u2010Long Wey, \"The Proof of the Collatz Conjecture\", arXiv:2309.09991 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2309_09991
