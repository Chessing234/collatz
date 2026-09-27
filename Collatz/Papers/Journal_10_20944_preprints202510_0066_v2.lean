import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Spencer, "The Resolution of the Collatz Conjecture: A Unified Arithmetic and Dynamical Framework", 2025.

Title: The Resolution of the Collatz Conjecture: A Unified Arithmetic and Dynamical Framework

Abstract (from harvested metadata, truncated):
We prove the Collatz Conjecture by establishing a complete arithmetic and dynamical closure of the map that sends: even n to n/2, and an odd n to 3n+1. Odd integers are classified by their residues modulo 18, and the least-admissible reverse lift determines a unique parent for each non-multiple of 3. This defines a deterministic, non-branching reverse graph. The only descending reverse case k=1 in residue class C_1 is arithmetically bounded by 3-adic valuation, eliminating the sole infinite descent corridor. All other admissible lifts strictly ascend, and no nontrivial odd cycles exist. Ternary cylinder sets encode every reverse path, and their affine recursion partitions N_odd without overl...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202510.0066.v2
-/

namespace Collatz.Papers.Journal_10_20944_preprints202510_0066_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Spencer, \"The Resolution of the Collatz Conjecture: A Unified Arithmetic and Dynamical Framework\", DOI:10.20944/preprints202510.0066.v2 [2025]."

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

end Collatz.Papers.Journal_10_20944_preprints202510_0066_v2
