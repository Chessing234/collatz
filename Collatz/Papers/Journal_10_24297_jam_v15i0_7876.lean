import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Anatoliy Nikolaychuk, "Supplement to the Collatz Conjecture", 2018.

Title: Supplement to the Collatz Conjecture

Abstract (from harvested metadata, truncated):
For any natural number was created the supplement sequence, that is convergent together with the original sequence. The parameter - index was defined, that is the same tor both sequences. This new method provides the following results: All natural numbers were distributed into different classes according to the corresponding indexes; The analytic formulas ( not by computer performed routine calculations) were produced, the formulas for groups of consecutive natural numbers of different lengths, having the same index; The new algorithm to find index for any natural number was constructed and proved.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.24297/jam.v15i0.7876
-/

namespace Collatz.Papers.Journal_10_24297_jam_v15i0_7876

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Anatoliy Nikolaychuk, \"Supplement to the Collatz Conjecture\", JOURNAL OF ADVANCES IN MATHEMATICS, DOI:10.24297/jam.v15i0.7876 [2018]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_24297_jam_v15i0_7876
