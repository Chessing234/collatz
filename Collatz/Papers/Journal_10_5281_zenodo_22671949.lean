import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Banazadeh Farhad, "A 4^r-Scaled Family of the Ternary (4k−1(2))/3 Collatz-Type Map: Exact Algebraic Conjugacy, Cycle Preservation, and Transfer of the \(10^9\) Finite Verification", 2026.

Title: A 4^r-Scaled Family of the Ternary (4k−1(2))/3 Collatz-Type Map: Exact Algebraic Conjugacy, Cycle Preservation, and Transfer of the \(10^9\) Finite Verification

Abstract (from harvested metadata, truncated):
This paper develops an exact algebraic scaling theory for the ternary (4k−1(2))/3 Collatz-type map introduced and computationally studied in the author's preceding work. The base system is defined on the positive integers not divisible by 3. For every integer r >= 0, a scaled state space is obtained by multiplying the base domain by 4^r. The corresponding scaled map has the two affine branches 4x − 4^r and 4x − 2·4^r, followed by complete removal of all factors of 3. The central result is an exact algebraic conjugacy between the base system and every member of the 4^r-scaled family. If y is a state of the base system, then the corresponding scaled state is x = 4^r y, and the maps satisfy T_r...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22671949
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22671949

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Banazadeh Farhad, \"A 4^r-Scaled Family of the Ternary (4k−1(2))/3 Collatz-Type Map: Exact Algebraic Conjugacy, Cycle Preservation, and Transfer of the \\(10^9\\) Finite Verification\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22671949 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22671949
