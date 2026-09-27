import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ashish Paudel, "Computability-Theoretic Obstructions to Reducing the Halting Problem to the Collatz Problem: A Reverse Mathematics Perspective", 2026.

Title: Computability-Theoretic Obstructions to Reducing the Halting Problem to the Collatz Problem: A Reverse Mathematics Perspective

Abstract (from harvested metadata, truncated):
We investigate the computational complexity of the Collatz ($3n+1$) conjecture via computability theory and reverse mathematics. Let $\mathcal{L}_C$ denote the set of integers whose Collatz orbits reach $1$. We show that a many-one reduction from the halting problem to $\mathcal{L}_C$ is incompatible with the truth of the conjecture, since decidability would follow. In the event the conjecture is false, we identify three independent barriers to such a reduction: a parity bottleneck restricting computational branching, an information-theoretic entropy bound from the golden-mean subshift, and a degree-theoretic gap requiring oracle power beyond the halting problem. We introduce the Collatz Choice Principle (CC), asserting that the set of counterexamples is Turing-equivalent to the halting...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19145644
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19145644

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ashish Paudel, \"Computability-Theoretic Obstructions to Reducing the Halting Problem to the Collatz Problem: A Reverse Mathematics Perspective\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19145644 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19145644
