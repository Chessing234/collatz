import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Banazadeh Farhad, "A Ternary (4k±1)/3 Collatz-Type Map and Its (4n±4^r)/3 Scaled Family", 2026.

Title: A Ternary (4k±1)/3 Collatz-Type Map and Its (4n±4^r)/3 Scaled Family

Abstract (from harvested metadata, truncated):
This work studies a ternary Collatz-type map of the form (4k±1)/3 and its infinite 4^r-scaled family. For every integer r >= 0, the scaled map is defined on the domain D_r = 4^r N by the relation T_r(4^r k) = 4^r T(k). The paper establishes an exact conjugacy between the base map and every member of the scaled family. In particular, T_r^j(4^r k) = 4^r T^j(k), so trajectories in each scaled domain correspond directly to trajectories of the base system under multiplication by 4^r. This structural relation transfers the dynamical behavior of the base map to the scaled family, including orbit structure and corresponding scaled trajectories. The paper also presents computational evidence for the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22228200
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22228200

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Banazadeh Farhad, \"A Ternary (4k±1)/3 Collatz-Type Map and Its (4n±4^r)/3 Scaled Family\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22228200 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22228200
