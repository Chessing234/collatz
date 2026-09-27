import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Budee U Zaman, "Exploring the Collatz Conjecture through Directed Graphs", arXiv:2402.00842 [2024].

Title: Exploring the Collatz Conjecture through Directed Graphs

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture is a well-known number theory puzzle that states that every positive integer would eventually converge to the trivial cycle of 1, 2, 1, 2,... when repeatedly exposed to a particular transformation. In this transformation, even numbers are divided in half, odd numbers are tripled, and one is added. In this study, we present a new method for creating a directed graph and using it to display and analyze Collatz sequences. Our technique creates what we call a Collatz directed graph by joining an endless number of simple directed graphs, each of which corresponds to a natural number. We show by careful mathematical analysis that all positive integers are included in this Collatz directed graph. Moreover, we give an evidence that verifies the Collatz conjecture by showing that the sole cycle in this graph is the trivial cycle of 1, 2, 1, 2,... We also prove that there is

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2402.00842
-/

namespace Collatz.Papers.Arxiv2402_00842

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Budee U Zaman, \"Exploring the Collatz Conjecture through Directed Graphs\", arXiv:2402.00842 [2024]."

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

end Collatz.Papers.Arxiv2402_00842
