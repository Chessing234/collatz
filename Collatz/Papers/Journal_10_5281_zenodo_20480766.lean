import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrei Fedotkin, "HARES ALWAYS RETURN. State Transition Graph and The Fabric: Objects to Solve 3x+1 and Lift the Veil over ax+1", 2026.

Title: HARES ALWAYS RETURN. State Transition Graph and The Fabric: Objects to Solve 3x+1 and Lift the Veil over ax+1

Abstract (from harvested metadata, truncated):
We introduce the State Transition Graph Sa and the Fabric Fa – a bijective, recursive weave of odd numbers in which multiples of a act as terminal leaves with no children, while every non-terminal node generates an infinite balcony of descendants. We provide proof of the Collatz conjecture. The Terminal Leaf Proof identifies multiples of 3 as the unique entry points of all trajectories and shows that they lock the door to infinity. The Graph Proof, expressed in the language of S3, establishes the same result through weak connectivity and the absence of non-trivial cycles. The two proofs are fully equivalent, mirroring the bijection between the Fabric and the Graph. We classify canonical root...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20480766
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20480766

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrei Fedotkin, \"HARES ALWAYS RETURN. State Transition Graph and The Fabric: Objects to Solve 3x+1 and Lift the Veil over ax+1\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20480766 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20480766
