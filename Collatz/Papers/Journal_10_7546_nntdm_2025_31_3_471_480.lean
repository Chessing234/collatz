import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mohammad Ansari, "Recursive sufficiency for the Collatz conjecture and computational verification", 2025.

Title: Recursive sufficiency for the Collatz conjecture and computational verification

Abstract (from harvested metadata, truncated):
We define the notion of recursive sufficiency for the Collatz conjecture and we use it to present some results concerning the computational verification of the conjecture. For any integer N ≥ 1 and any recursively sufficient set F, it is proved that all integers in the interval [1, N] satisfy the conjecture if and only if F ∩ [1, N] satisfies the conjecture. We offer a sequence of sieves for which the corresponding sequence of elimination percentages tends to 100\%, and as a result, for any integer P arbitrarily close to 100, we give a sieve whose elimination percentage is at least P%. Also, we prove that if N=2(3^n)+1 is the largest known integer for which all integers 1, 2, ..., N satisfy...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.7546/nntdm.2025.31.3.471-480
-/

namespace Collatz.Papers.Journal_10_7546_nntdm_2025_31_3_471_480

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mohammad Ansari, \"Recursive sufficiency for the Collatz conjecture and computational verification\", Notes on Number Theory and Discrete Mathematics, DOI:10.7546/nntdm.2025.31.3.471-480 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_7546_nntdm_2025_31_3_471_480
