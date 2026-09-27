import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Collatz computation sequence for sufficiently large integers is a pseudo-random bit sequence", 2026.

Title: Collatz computation sequence for sufficiently large integers is a pseudo-random bit sequence

Abstract (from harvested metadata, truncated):
Collatz conjecture states that each positive integer will return to 1 after two computations — either [Formula: see text] when x is odd or [Formula: see text] when x is even. We denote [Formula: see text] as ‘I’ and [Formula: see text] as ‘O’. Given a starting integer x, the computational sequence from x to 1 can be looked as a string consisting of ‘I’ and ‘O’. We call this sequence (string) as the dynamics of x. The key results are as follows: (1) To verify the Collatz conjecture, we randomly select an extremely large integer and verify whether it can return to 1. The largest one has been verified by us has 6,000,000 bits, which is overwhelmingly much larger than currently verified by other...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1142/s2811007225500233
-/

namespace Collatz.Papers.Journal_10_1142_s2811007225500233

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Collatz computation sequence for sufficiently large integers is a pseudo-random bit sequence\", Mathematics Open, DOI:10.1142/s2811007225500233 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1142_s2811007225500233
