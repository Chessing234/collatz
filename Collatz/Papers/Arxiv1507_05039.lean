import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mallet, Nicolas, "Trial for a proof of the Syracuse conjecture", arXiv:1507.05039 [2015].

Title: Trial for a proof of the Syracuse conjecture

Abstract (from OpenAlex metadata, truncated):
The infamous 3x+1 conjecture spread by Lothar Collatz in 1952, despite its elementary formulation, remained unproved for over 60 years. From the heuristical probabilistic approach to the complex mapping of the algorithm, the scientific community has fetched for many methods to try to prove it formally, and thus, mathematicians like Erdos tend to believe that "mathematics are not yet ready for such problems". In this research report, covering domains like algebra and graph theory, it is shown a trial of proof of the conjecture by disproval of its two antitheses: the existence of an ever-growing Syracuse suite and the existence of a cycle different from the cycle 4,2,1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1507.05039
-/

namespace Collatz.Papers.Arxiv1507_05039

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mallet, Nicolas, \"Trial for a proof of the Syracuse conjecture\", arXiv:1507.05039 [2015]."

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

end Collatz.Papers.Arxiv1507_05039
