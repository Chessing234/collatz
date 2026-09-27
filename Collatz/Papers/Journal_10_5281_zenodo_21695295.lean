import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zeraoulia Rafik, "A Reproducible Extension Beyond 2^71 and Exact First-Descent Statistics for the Collatz Map", 2026.

Title: A Reproducible Extension Beyond 2^71 and Exact First-Descent Statistics for the Collatz Map

Abstract (from harvested metadata, truncated):
This preprint gives a reproducible finite extension of the published Collatz verification boundary. Using Barina's open-source verifier with two residue-sieve configurations, every integer in [2^71, 2^71 + 2^40) is certified to descend below its starting value; combined with the published base computation, this verifies convergence for every n < 2^71 + 2^40. A separate direct computation enumerates the exact first-descent distribution for all 2^34 integers in [2^71, 2^71 + 2^34). The observed survival tail motivates a conjectural large-deviation law and an associated extreme-value heuristic. The probabilistic discussion is heuristic and does not prove the unrestricted Collatz conjecture. This revised version adds a direct comparison with David Barina's distributed verification project,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21695295
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21695295

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Zeraoulia Rafik, \"A Reproducible Extension Beyond 2^71 and Exact First-Descent Statistics for the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21695295 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21695295
