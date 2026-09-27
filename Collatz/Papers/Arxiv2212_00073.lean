import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Naouel Boulkaboul, "$3n+3^k$: New Perspective on Collatz Conjecture", arXiv:2212.00073 [2022].

Title: $3n+3^k$: New Perspective on Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
Collatz conjecture is generalized to $3n+3^k$ ($k\in N$). Operating as usual, every sequence seems to reach $3^k$ and end up in the loop $3^k, 4.3^k, 2.3^k,3^k$. The usual $3n+1$ conjecture is recovered for $k=0$. For $k>0$, we noticed the existence of a sequence of period 3, namely, $3^{k-1}, 2.3^k, 3^k$, alongside the cycle $4.3^k, 2.3^k,3^k$ encountered in the $3n+1 (k=0)$ sequence. A term formula of the $3n+3^k$ conjecture has been derived, and hence the total stopping time.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2212.00073
-/

namespace Collatz.Papers.Arxiv2212_00073

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Naouel Boulkaboul, \"$3n+3^k$: New Perspective on Collatz Conjecture\", arXiv:2212.00073 [2022]."

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


end Collatz.Papers.Arxiv2212_00073
