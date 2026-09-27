import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for San Min Wang, "An E-sequence approach to the 3x + 1 problem", arXiv:1809.02278 [2018].

Title: An E-sequence approach to the 3x + 1 problem

Abstract (from OpenAlex metadata, truncated):
For any odd positive integer $x$, define $(x_n)_{n\geqslant 0} $ and $(a_n )_{n\geqslant 1} $ by setting $x_{0}=x, \,\, x_n =\cfrac{3x_{n-1} +1}{2^{a_n }}$ such that all $x_n $ are odd. The 3x+1 problem asserts that there is an $x_n =1$ for all $x$. Usually, $(x_n )_{n\geqslant 0} $ is called the trajectory of $x$. In this paper, we concentrate on $(a_n )_{n\geqslant 1} $ and call it the E-sequence of $x$. The idea is that, we generalize E-sequences to all infinite sequence $(a_n )_{n\geqslant 1} $ of positive integers and consider all these generalized E-sequences. We then define $(a_n )_{n\geqslant 1} $ to be $Ω-$convergent to $x$ if it is the E-sequence of $x$ and to be $Ω-$divergent if it is not the E-sequence of any odd positive integer. We prove a remarkable fact that the $Ω-$divergence of all non-periodic E-sequences implies the periodicity of $(x_n )_{n\geqslant 0} $ for all $x_0

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1809.02278
-/

namespace Collatz.Papers.Arxiv1809_02278

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "San Min Wang, \"An E-sequence approach to the 3x + 1 problem\", arXiv:1809.02278 [2018]."

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


end Collatz.Papers.Arxiv1809_02278
