import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Masayoshi Kaneda, "Two remarks on the Collatz cycle conjecture", arXiv:1010.6206 [2010].

Title: Two remarks on the Collatz cycle conjecture

Abstract (from OpenAlex metadata, truncated):
We give a short proof of Belaga's result on bounds to perigees of $(3x+d)$-cycles of a given oddlength. We also reformulate the Collatz cycle conjecture which is rather a algorithmic problem into a purely arithmetic problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1010.6206
-/

namespace Collatz.Papers.Arxiv1010_6206

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Masayoshi Kaneda, \"Two remarks on the Collatz cycle conjecture\", arXiv:1010.6206 [2010]."

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

end Collatz.Papers.Arxiv1010_6206
