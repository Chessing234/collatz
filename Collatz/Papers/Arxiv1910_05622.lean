import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vicente Padilla, "3x + 1 Problem. Syracuse Conjecture", arXiv:1910.05622 [2019].

Title: 3x + 1 Problem. Syracuse Conjecture

Abstract (from OpenAlex metadata, truncated):
In this paper; we prove that all sequences can be broken up in cycles. Each cycle follows the same pattern: 1) Upward trajectory. Odd and even numbers alternate until the cycle reaches an upper bound 2) Downward trajectory. Two or more consecutive even numbers follow until it reaches another odd number. At this point, it's the beginning of the following cycle. Any sequence is evidently made of many consecutive cycles. In order to prove the conjecture, we build two sequences. The first sequence starts from any odd number. The sequence unfolds one cycle after the another. After each cycle, we build a second sequence that is built following a parallel path to the previous one, but adapting the last cycle to ensure it converges down to 1. In other words, their cycles have the same pattern of upward and downward steps except for the very last cycle. Finally, we prove that both sequences must 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1910.05622
-/

namespace Collatz.Papers.Arxiv1910_05622

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vicente Padilla, \"3x + 1 Problem. Syracuse Conjecture\", arXiv:1910.05622 [2019]."

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


end Collatz.Papers.Arxiv1910_05622
