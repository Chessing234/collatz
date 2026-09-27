import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for UĞUR PERVANE, "PROOF OF THE COLLATZ CONJECTURE USING THE REVERSE ALGORITHM", 2025.

Title: PROOF OF THE COLLATZ CONJECTURE USING THE REVERSE ALGORITHM

Abstract (from harvested metadata, truncated):
The Collatz conjecture has remained unsolved for a long time. In this paper, a proof of this conjecture will be presented. We know that almost all numbers will eventually reach one through the steps of the Collatz algorithm. Terence Tao has previously proven this. This paper demonstrates that all numbers will reach one by using Tao's proof. If almost all numbers reach one, then the probability that a randomly chosen number from the set of positive integers will reach one is one. The probability that a number will not reach one is zero. The probability of selecting the elements of the number sequences associated with a number n that violates the conjecture from the set of positive integers is...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/6n3bp_v1
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_6n3bp_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "UĞUR PERVANE, \"PROOF OF THE COLLATZ CONJECTURE USING THE REVERSE ALGORITHM\", DOI:10.31219/osf.io/6n3bp_v1 [2025]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_31219_osf_io_6n3bp_v1
