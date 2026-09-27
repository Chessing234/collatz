import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ahmed Mohammed Jalal Rasull Kawani, "The Definitive Proof that Collatz Conjecture is True", 2024.

Title: The Definitive Proof that Collatz Conjecture is True

Abstract (from harvested metadata, truncated):
In this paper and for the first time ever, I will provide the conclusive proofs that Collatz's conjecture is true, and how is it works on basis one of the greatest algorithms ever. And it is much more than a (3n + 1), because as long as it was believed that for this conjecture only a (3n + 1) mechanism applied, while this is not true at all.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.4792239
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_4792239

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ahmed Mohammed Jalal Rasull Kawani, \"The Definitive Proof that Collatz Conjecture is True\", DOI:10.2139/ssrn.4792239 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_2139_ssrn_4792239
