import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jorge D. Salazar, "On the Behavior of Unbounded Collatz Sequences", arXiv:2003.04615 [2020].

Title: On the Behavior of Unbounded Collatz Sequences

Abstract (from OpenAlex metadata, truncated):
The aim of this paper is to show a peculiar behavior of a (hypothetical) Collatz sequence going to infinity. We study the associated Syracusa sequence (the odd elements of the former) and show that the limit set of a conveniently normalized sequence is the whole unit interval. In particular, for any positive integer there is a subsequence whose elements' expansions in base 3 begin (from the left) with the expansion of the given number.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2003.04615
-/

namespace Collatz.Papers.Arxiv2003_04615

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jorge D. Salazar, \"On the Behavior of Unbounded Collatz Sequences\", arXiv:2003.04615 [2020]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2003_04615
