import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rozier, Olivier, Terracol, Claude, "Paradoxical behavior in Collatz sequences", arXiv:2502.00948 [2025].

Title: Paradoxical behavior in Collatz sequences

Abstract (from OpenAlex metadata, truncated):
On the set of positive integers, we consider the iterative process that maps $n$ to either $\frac{3n+1}{2}$ or $\frac{n}{2}$ depending on the parity of $n$. The Collatz conjecture states that all such sequences eventually enter the trivial cycle $(1,2)$. In a seminal paper, Terras further conjectured that the proportion of odd terms encountered when starting with an integer $n\geq2$ is sufficient to determine its stopping time, namely, the number of iterations needed to descend below $n$. However, when iterating beyond the stopping time, there exist "paradoxical" sequences of finite length whose first term is unexpectedly exceeded, given the proportion of odd terms. In the present study, we show that this non-typical behavior is closely related to the Collatz conjecture. Furthermore, we find that it most likely occurs finitely many times, thus lending support to Terras' conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2502.00948
-/

namespace Collatz.Papers.Arxiv2502_00948

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rozier, Olivier and Terracol, Claude, \"Paradoxical behavior in Collatz sequences\", arXiv:2502.00948 [2025]."

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

end Collatz.Papers.Arxiv2502_00948
