import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren and Ruiyang Xiao, "How to Fast Verify Collatz Conjecture by Automata", 2019.

Title: How to Fast Verify Collatz Conjecture by Automata

Abstract (from harvested metadata, truncated):
To verify Collatz conjecture for a given integer, we need to justify whether or not the given starting number goes to 1 finally. Current method computes 3*x+1 and x/2 one by one. In this paper, we propose an automata-based algorithm to compute the process in a batch with m steps - (3*x+1)2 or x/2. We also propose reduced Collatz conjecture and we prove it is equivalent to Collazt conjecture. We also point out that original dynamics is the combination of reduced dynamics. (Original dynamics is a serial of occurred 3*x+1 and x/2 computation in the process from a starting number to 1; Reduced dynamics is a serial of occurred 3*x+1 and x/2 computation in the process from a starting number to the first transformed number that is less than the starting number.) We study the properties of...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/hpcc/smartcity/dss.2019.00382
-/

namespace Collatz.Papers.Journal_10_1109_hpcc_smartcity_dss_2019_00382

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren and Ruiyang Xiao, \"How to Fast Verify Collatz Conjecture by Automata\", 2019 IEEE 21st International Conference on High Performance Computing and Communications; IEEE 17th International Conference on Smart City; IEEE 5th International Conference on Data Science and Systems (HPCC/SmartCity/DSS), DOI:10.1109/hpcc/smartcity/dss.2019.00382 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_hpcc_smartcity_dss_2019_00382
