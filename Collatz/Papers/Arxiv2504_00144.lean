import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for M. Yasser, "Recursive Approach for Proving Collatz Conjecture", arXiv:2504.00144 [2025].

Title: Recursive Approach for Proving Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
In this study, the authors investigate the Collatz conjecture using a frequency-based iterative approach, demonstrating that all natural numbers ultimately converge to a reduced value with an increasing frequency rate, eventually leading to a cyclic loop. Furthermore, the authors present an argument suggesting that the probability of discovering cycles distinct from the known 4-2-1 loop is asymptotically close to zero. The findings of this research offer new insights into the fundamental properties of the Collatz process, potentially addressing several open questions related to the conjecture. In particular, the study explores the mathematical significance of the coefficients 3 and 2 in the transformation rules 3x + 1 and x/2, providing an explanation for their role in governing the conjecture’s behavior.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2504.00144
-/

namespace Collatz.Papers.Arxiv2504_00144

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "M. Yasser, \"Recursive Approach for Proving Collatz Conjecture\", arXiv:2504.00144 [2025]."

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

end Collatz.Papers.Arxiv2504_00144
