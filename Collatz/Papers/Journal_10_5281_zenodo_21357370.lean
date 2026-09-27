import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for nadal ferra, "A Dissipative Attractor Approach to the Collatz Problem: Non-Divergence, Cycle Constraints and Diophantine Obstructions", 2026.

Title: A Dissipative Attractor Approach to the Collatz Problem: Non-Divergence, Cycle Constraints and Diophantine Obstructions

Abstract (from harvested metadata, truncated):
This work presents an analytical approach to the Collatz problem (3n+1 problem) based on a dissipative dynamical systems framework. The proposed framework combines three complementary components: a non-divergence analysis based on negative bit-length drift, constraints on possible non-trivial cycles through logarithmic and arithmetic relations, and Diophantine considerations involving primitive prime divisors. Computational experiments performed using CUDA parallel processing are included as supplementary material to investigate the numerical behaviour of Collatz trajectories and the proposed dissipative structure. The manuscript is intended to provide a mathematical framework for further analysis and independent verification of the presented arguments.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21357370
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21357370

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "nadal ferra, \"A Dissipative Attractor Approach to the Collatz Problem: Non-Divergence, Cycle Constraints and Diophantine Obstructions\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21357370 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21357370
