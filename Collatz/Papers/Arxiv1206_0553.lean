import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alec Edgington, "The autoconjugacy of a generalized Collatz map", arXiv:1206.0553 [2012].

Title: The autoconjugacy of a generalized Collatz map

Abstract (from OpenAlex metadata, truncated):
Many of the 2-adic properties of the 3x+1 map generalize to the analogous mx+r map, where m and r are odd integers. We introduce the corresponding autoconjugacy map, prove some simple properties of it and make some further conjectures in the general setting, including weak versions of the periodicity and divergent trajectories conjectures.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1206.0553
-/

namespace Collatz.Papers.Arxiv1206_0553

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alec Edgington, \"The autoconjugacy of a generalized Collatz map\", arXiv:1206.0553 [2012]."

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

end Collatz.Papers.Arxiv1206_0553
