import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gaurav Goyal, "General Dynamics and Generation Mapping for Collatz-Type Sequences", arXiv:2408.02050 [2024].

Title: General Dynamics and Generation Mapping for Collatz-Type Sequences

Abstract (from OpenAlex metadata, truncated):
Let an odd integer \(\mathcal{X}\) be expressed as $\left\{\sum\limits_{M > m} b_M 2^M\right\} + 2^m - 1,$ where $b_M \in \{0, 1\}$ and $2^m - 1$ is referred to as the Governor. In Collatz-type functions, a high index Governor is eventually reduced to $2^1 - 1$. For the $3\mathcal{Z} + 1$ sequence, the Governor occurring in the Trivial cycle is $2^1 - 1$, while for the $5\mathcal{Z} + 1$ sequence, the Trivial Governors are $2^2 - 1$ and $2^1 - 1$. Therefore, in these specific sequences, the Collatz function reduces the Governor $2^m - 1$ to the Trivial Governor $2^{\mathcal{T}} - 1$. Once this Trivial Governor is reached, it can evolve to a higher index Governor through interactions with other terms. This feature allows $\mathcal{X}$ to reappear in a Collatz-type sequence, since $2^m - 1 = 2^{m - 1} + \cdots + 2^{\mathcal{T} + 1} + 2^{\mathcal{T}} + (2^{\mathcal{T}} - 1).$ Thus, if $\mat

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2408.02050
-/

namespace Collatz.Papers.Arxiv2408_02050

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gaurav Goyal, \"General Dynamics and Generation Mapping for Collatz-Type Sequences\", arXiv:2408.02050 [2024]."

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

end Collatz.Papers.Arxiv2408_02050
