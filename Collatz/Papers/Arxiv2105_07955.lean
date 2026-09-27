import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fabian S. Reid, "The Visual Pattern in the Collatz Conjecture and Proof of No Non-Trivial Cycles", arXiv:2105.07955 [2021].

Title: The Visual Pattern in the Collatz Conjecture and Proof of No Non-Trivial Cycles

Abstract (from OpenAlex metadata, truncated):
We present the long sought visual pattern in the Collatz problem with the aid of a logarithmic spiral. Using this newly discovered pattern, we show that the Collatz problem is linked to primes via Jacobsthal numbers. We then prove that no non-trivial cycles exist on the spiral and by extension in the Collatz problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2105.07955
-/

namespace Collatz.Papers.Arxiv2105_07955

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fabian S. Reid, \"The Visual Pattern in the Collatz Conjecture and Proof of No Non-Trivial Cycles\", arXiv:2105.07955 [2021]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2105_07955
