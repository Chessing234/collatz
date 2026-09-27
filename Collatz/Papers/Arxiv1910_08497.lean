import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Pablo Castañeda, "A dynamical approach towards Collatz conjecture", arXiv:1910.08497 [2019].

Title: A dynamical approach towards Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
The present work focuses on the study of the renowned Collatz conjecture, also known as the $3x +1$ problem. The distinguished analysis approach lies on the dynamics of an iterative map in binary form. A new estimation of the enlargement of iterated numbers is given. Within the associated iterative map, characteristic periods for periodic orbits are identified.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1910.08497
-/

namespace Collatz.Papers.Arxiv1910_08497

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Pablo Casta\u00f1eda, \"A dynamical approach towards Collatz conjecture\", arXiv:1910.08497 [2019]."

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


end Collatz.Papers.Arxiv1910_08497
