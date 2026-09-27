import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Robert Tremblay, "Generalized 3x + 1 Mappings : counting cycles", arXiv:1909.00213 [2019].

Title: Generalized 3x + 1 Mappings : counting cycles

Abstract (from OpenAlex metadata, truncated):
We demonstrate that the number of cycles for two problems of the family of generalized 3x+1 mappings is possible finite.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1909.00213
-/

namespace Collatz.Papers.Arxiv1909_00213

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Robert Tremblay, \"Generalized 3x + 1 Mappings : counting cycles\", arXiv:1909.00213 [2019]."

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


end Collatz.Papers.Arxiv1909_00213
