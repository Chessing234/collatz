import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Barina and W. C. Maat, "$3n + 3^k$ Problem", arXiv:2602.05732 [2026].

Title: $3n + 3^k$ Problem

Abstract (from OpenAlex metadata, truncated):
The Collatz problem is generalized into $3n + 3^k$ problem. It is shown that as long as the Collatz function iterates converge to the cycle passing through the number 1, the $3n + 3^k$ sequence converges to the cycle passing through the number $3^k$ for arbitrary positive integers $n$ and $k$. The proof shows that the sequence of $3n + 3^k$ function iterates for a number $3^k n$ is exactly the sequence of the Collatz function iterates for $n$ multiplied by $3^k$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2602.05732
-/

namespace Collatz.Papers.Arxiv2602_05732

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Barina and W. C. Maat, \"$3n + 3^k$ Problem\", arXiv:2602.05732 [2026]."

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


end Collatz.Papers.Arxiv2602_05732
