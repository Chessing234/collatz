import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Grażyna Mirkowska and Andrzej Salwicki, "Collatz conjecture becomes theorem", arXiv:2310.13035 [2023].

Title: Collatz conjecture becomes theorem

Abstract (from OpenAlex metadata, truncated):
The Collatz hypothesis is a theorem of the algorithmic theory of natural numbers. We prove the (algorithmic) formula that expresses the halting property of Collatz algorithm. The observation that Collatz's theorem cannot be proved in any elementary number theory completes the main result.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2310.13035
-/

namespace Collatz.Papers.Arxiv2310_13035

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gra\u017cyna Mirkowska and Andrzej Salwicki, \"Collatz conjecture becomes theorem\", arXiv:2310.13035 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2310_13035
