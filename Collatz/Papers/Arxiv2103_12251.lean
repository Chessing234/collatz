import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vinny Pagano, "A $p$-adic Approach To Piecewise Polynomial Dynamical Systems", arXiv:2103.12251 [2021].

Title: A $p$-adic Approach To Piecewise Polynomial Dynamical Systems

Abstract (from OpenAlex metadata, truncated):
Using $p$-adic numbers, we partially categorize the cycles of a sizable class of polynomial dynamical systems. In turn, we prove a few results related to the non-trivial cycles of the $\textit{Collatz map}$ $\text{Col} : \mathbb{Z}_+ \to \mathbb{Z}_+$ defined by $$\text{Col}(n) = \begin{cases} 3n + 1, & n \text{ is odd;} \\ n/2, & \text{otherwise.}\end{cases}$$ Proving the non-existence of non-trivial Collatz cycles would reduce the Collatz conjecture to whether the Collatz map can diverge to infinity.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2103.12251
-/

namespace Collatz.Papers.Arxiv2103_12251

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vinny Pagano, \"A $p$-adic Approach To Piecewise Polynomial Dynamical Systems\", arXiv:2103.12251 [2021]."

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


end Collatz.Papers.Arxiv2103_12251
