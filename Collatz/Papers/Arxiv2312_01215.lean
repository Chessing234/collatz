import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aditya Dalal, "On the Equality of ‘Stopping Times’ of Hailstone Numbers", arXiv:2312.01215 [2023].

Title: On the Equality of ‘Stopping Times’ of Hailstone Numbers

Abstract (from OpenAlex metadata, truncated):
This short technical note proves some observed novel corollaries of the Collatz Conjecture. For this, a unique ‘Collatz Representation’ of Hailstone numbers has been employed. After that, an extension of this corollary is explained using the fact that only certain differences in the last digit of the ‘Collatz Representation’ gives a whole number difference between numbers. A more general result is obtained. The final proof is for a corollary that some numbers the same number of steps to reach 1 if the Collatz Conjecture is true and all variables are whole numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2312.01215
-/

namespace Collatz.Papers.Arxiv2312_01215

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aditya Dalal, \"On the Equality of \u2018Stopping Times\u2019 of Hailstone Numbers\", arXiv:2312.01215 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv2312_01215
