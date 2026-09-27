import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gaurav Goyal, "Crafting Integers That ‘May’ Diverge for Collatz Sequence", arXiv:2407.02192 [2024].

Title: Crafting Integers That ‘May’ Diverge for Collatz Sequence

Abstract (from OpenAlex metadata, truncated):
Let an odd integer be represented as $\sum \limits_{n > m} 2^n + 2^m - 1$ for $m \geq 1$. To transform $2^m - 1$ according to the Collatz rules, the $3x + 1$ step is applied, resulting in the even integer $2^{m + 1} + 2^m - 2$. This even integer, being exactly once divisible by 2, becomes the next odd integer $2^m + 2^{m - 1} - 1$. This represents the growth phase, as exactly one even step follows an odd step. However, while the overall value of the integer increases, terms with decreasing indices are generated after each odd-even cycle. After $m$ such cycles, a term $2^{m - m}$ (which equals 1) is generated, canceling the negative 1. Additional even steps are then performed until the integer becomes odd again, which occurs when the next smallest index becomes zero. The positive 1 thus obtained is written as $2^1 - 1$. If uninterrupted, the term $2^1 - 1$ has the trivial cycle $2^1 - 1 \

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2407.02192
-/

namespace Collatz.Papers.Arxiv2407_02192

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gaurav Goyal, \"Crafting Integers That \u2018May\u2019 Diverge for Collatz Sequence\", arXiv:2407.02192 [2024]."

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

end Collatz.Papers.Arxiv2407_02192
