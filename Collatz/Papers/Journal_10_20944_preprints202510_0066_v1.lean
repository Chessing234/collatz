import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Spencer M., "The Resolution of the Collatz Conjecture via a Unified Framework: Local Residue Dynamics and Global Ladder Coverage", 2025.

Title: The Resolution of the Collatz Conjecture via a Unified Framework: Local Residue Dynamics and Global Ladder Coverage

Abstract (from harvested metadata, truncated):
The Collatz Conjecture asks whether repeated iteration of a simple map always reaches the trivial cycle 1 → 4 → 2 → 1. The rule is: if a number is even, divide it by two; if a number is odd, multiply it by 3 and add one. We prove that the dynamics of this map are governed by two frameworks whose union establishes a duality. The recursive local view shows that every odd integer generates a unique parent–child trajectory, ensuring complete local coverage with no gaps. The iterative global view shows that parent–child offsets extend to arithmetic ladders whose higher lifts systematically fill all odd residues, guaranteeing complete coverage of the odd integers. These structures are isomorphic: each recursive relation corresponds to an offset increment, and together they form a single unified...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202510.0066.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202510_0066_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Spencer M., \"The Resolution of the Collatz Conjecture via a Unified Framework: Local Residue Dynamics and Global Ladder Coverage\", DOI:10.20944/preprints202510.0066.v1 [2025]."

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

end Collatz.Papers.Journal_10_20944_preprints202510_0066_v1
