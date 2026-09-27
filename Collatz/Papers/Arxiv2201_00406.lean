import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Christian Hercher, "There are no Collatz-m-Cycles with $m\leq 91$", arXiv:2201.00406 [2022].

Title: There are no Collatz-m-Cycles with $m\leq 91$

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture (or ``Syracuse problem'') considers recursively-defined sequences of positive integers where $n$ is succeeded by $\tfrac{n}{2}$, if $n$ is even, or $\tfrac{3n+1}{2}$, if $n$ is odd. The conjecture states that for all starting values $n$ the sequence eventually reaches the trivial cycle $1, 2, 1, 2, \ldots$ . We are interested in the existence of nontrivial cycles. Let $m$ be the number of local minima in such a nontrivial cycle. Simons and de Weger proved that $m \geq 76$. With newer bounds on the range of starting values for which the Collatz conjecture has been checked, one gets $m \geq 83$. In this paper, we prove $m \geq 92$. The last part of this paper considers what must be proven in order to raise the number of odd members a nontrivial cycle has to have to the next bound -- that is, to at least $K\geq1.375\cdot 10^{11}$. We prove that it suffices to show that, for every integer smaller than or equal to $1536\cdot2^{60}=3\cdot2^{69}$, the respective Collatz

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2201.00406
-/

namespace Collatz.Papers.Arxiv2201_00406

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Christian Hercher, \"There are no Collatz-m-Cycles with $m\\leq 91$\", arXiv:2201.00406 [2022]."

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


end Collatz.Papers.Arxiv2201_00406
