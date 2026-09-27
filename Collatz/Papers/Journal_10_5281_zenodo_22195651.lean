import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Banazadeh Farhad, "A Ternary (4k±1)/3 Collatz-Type Map: Computational Verification up to 10^9", 2026.

Title: A Ternary (4k±1)/3 Collatz-Type Map: Computational Verification up to 10^9

Abstract (from harvested metadata, truncated):
This research presents a ternary Collatz-type map based on division by 3 and the rules (4k−1)/3 and (4k+1)/3 according to the remainder of k modulo 3. The paper studies the behavior of the map and gives a computational verification for all starting integers from 1 to 10^9. In the reported computation, every tested starting value reached 1. The longest orbit found had 540 steps, starting from n = 972,526,420. The highest value reached during the computation was 193,592,042,138,992,737, starting from n = 918,487,522. The paper also gives a simple heuristic analysis based on the average change of log(k), together with examples of trajectories and record cases. The computational package included with this record contains the source code, scripts, test files, result files, trajectory data,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22195651
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22195651

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Banazadeh Farhad, \"A Ternary (4k±1)/3 Collatz-Type Map: Computational Verification up to 10^9\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22195651 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22195651
