import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sensen Chen et al., "The Periodicity to a Kind of Generalized Collatz Problem", arXiv:1903.03365 [2019].

Title: The Periodicity to a Kind of Generalized Collatz Problem

Abstract (from OpenAlex metadata, truncated):
The Collatz problem is related to the fixed point problem, and is widely used in mathematics. It has attracted a wide range of math enthusiasts, but is still difficult to solve. So, this article aimed to study the extension of the Collatz problem, more widely, in k-adic. We define a new sequence called Z transformation sequence. Under a suitable assumptions, we can prove that the limit set of the Z transformation sequence must be M={1,2}.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1903.03365
-/

namespace Collatz.Papers.Arxiv1903_03365

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sensen Chen et al., \"The Periodicity to a Kind of Generalized Collatz Problem\", arXiv:1903.03365 [2019]."

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


end Collatz.Papers.Arxiv1903_03365
