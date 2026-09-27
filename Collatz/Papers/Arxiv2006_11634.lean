import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Brier, Éric, Géraud-Stewart, Rémi, Naccache, David, "A Fractional $3n+1$ Conjecture", arXiv:2006.11634 [2020].

Title: A Fractional $3n+1$ Conjecture

Abstract (from OpenAlex metadata, truncated):
In this paper we introduce and discuss the sequence of \emph{real numbers} defined as $u_0 \in \mathbb R$ and $u_{n+1} = Δ(u_n)$ where \begin{equation*} Δ(x) = \begin{cases} \frac{x}{2} &\text{if } \operatorname{frac}(x)<\frac{1}{2} \\[4px] \frac{3x+1}{2} & \text{if } \operatorname{frac}(x)\geq\frac{1}{2} \end{cases} \end{equation*} This sequence is reminiscent of the famous Collatz sequence, and seems to exhibit an interesting behaviour. Indeed, we conjecture that iterating $Δ$ will eventually either converge to zero, or loop over sequences of real numbers with integer parts $1,2,4,7,11,18,9,4,7,3,5,9,4,7,11,18,9,4,7,3,6,3,1,2,4,7,3,6,3$.
  We prove this conjecture for $u_0 \in [0, 100]$. Extending the proof to larger fixed values seems to be a matter of computing power. The authors pledge to offer a reward to the first person who proves or refutes the conjecture completely -- with a pr

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2006.11634
-/

namespace Collatz.Papers.Arxiv2006_11634

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Brier, \u00c9ric et al., \"A Fractional $3n+1$ Conjecture\", arXiv:2006.11634 [2020]."

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

end Collatz.Papers.Arxiv2006_11634
