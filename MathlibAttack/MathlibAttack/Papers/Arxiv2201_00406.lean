import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Christian Hercher, "There are no Collatz-m-Cycles with $m\leq 91$", arXiv:2201.00406 [2022].

Title: There are no Collatz-m-Cycles with $m\leq 91$

Abstract (truncated):
The Collatz conjecture (or ``Syracuse problem'') considers recursively-defined sequences of positive integers where $n$ is succeeded by $\tfrac{n}{2}$, if $n$ is even, or $\tfrac{3n+1}{2}$, if $n$ is odd. The conjecture states that for all starting values $n$ the sequence eventually reaches the trivial cycle $1, 2, 1, 2, \ldots$ . We are interested in the existence of nontrivial cycles. Let $m$ be the number of local minima in such a nontrivial cycle. Simons and de Weger proved that $m \geq 76$. With newer bounds on the range of starting values for which the Collatz conjecture has been checked, one gets $m \geq 83$. In this paper, we prove $m \geq 92$. The last part of this paper considers what must be proven in order to raise the number of odd members a nontrivial cycle has to have to the next bound -- that is, to at least $K\geq1.375\cdot 10^{11}$. We prove that it suffices to show tha

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2201.00406
-/

namespace MathlibAttack.Papers.Arxiv2201_00406

open MathlibAttack.Papers

def citation : String := "Christian Hercher, \"There are no Collatz-m-Cycles with $m\\leq 91$\", arXiv:2201.00406 [2022]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2201_00406
