import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Shiraishi H and Shiraishi H., "<strong></strong>Simplified Proof of the Collatz Conjecture Using Regularity General solution‐Calculation Method by Multiples of 6 and Remainder", 2024.

Title: <strong></strong>Simplified Proof of the Collatz Conjecture Using Regularity General solution‐Calculation Method by Multiples of 6 and Remainder

Abstract (from harvested metadata, truncated):
In solving the Collatz conjecture, it turns out that if we let all integers k be 6n, 6n+1, 6n+2, 6n+3, 6n+4, 6n+5, then we can solve the Collatz conjecture periodically. The Collatz conjecture states that for any positive integer P (initial value), if n is even, divide n by 2; if n is odd, repeat the rule of multiplying n by 3 and adding 1, which always converges to 1. One open problem has been proved by this paper. The authors hope to contribute to the mathematical community by presenting simple proofs of conjectures in the history of mathematics such as the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202408.0021.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202408_0021_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Shiraishi H and Shiraishi H., \"<strong></strong>Simplified Proof of the Collatz Conjecture Using Regularity General solution‐Calculation Method by Multiples of 6 and Remainder\", DOI:10.20944/preprints202408.0021.v1 [2024]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_20944_preprints202408_0021_v1
