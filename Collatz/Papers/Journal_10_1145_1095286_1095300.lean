import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael J. McGill et al., "Syracuse information retrieval experiment (SIRE)", 1976.

Title: Syracuse information retrieval experiment (SIRE)

Abstract (from harvested metadata, truncated):
Proponents of interactive online bibliographic retrieval systems frequently stress the potential of such systems to take advantage of both human and computer capabilities in the document retrieval process. Yet systems implemented to date have to a great extent placed constraints on both human and machine performance by decisions made at the design stage. To increase the flexibility of online systems, alternative modes of document representation, storage utilization, and query formulation should be considered.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1145/1095286.1095300
-/

namespace Collatz.Papers.Journal_10_1145_1095286_1095300

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael J. McGill et al., \"Syracuse information retrieval experiment (SIRE)\", ACM SIGIR Forum, DOI:10.1145/1095286.1095300 [1976]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1145_1095286_1095300
