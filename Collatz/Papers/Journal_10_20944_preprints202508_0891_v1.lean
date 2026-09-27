import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hahn, Kirk, "Collatz Conjecture Is True for All Positive Integers", 2025.

Title: Collatz Conjecture Is True for All Positive Integers

Abstract (from harvested metadata, truncated):
This work offers formal proofs which were enabled by a change in perspective from studying individual integer iterations to analyzing how the conjecture's rules organize the positive integers. The proofs rigorously demonstrate the satisfaction of several critical criteria: the universal inclusion of all positive integers within the proof's scope; the disclosure of a simple and predictable pattern among the numbers; the conclusive absence of any major loops; the demonstration that no number continuously increases indefinitely without eventually decreasing; and the ultimate convergence of all positive integers to 1 when subjected to the Collatz iteration rules. Formal verification of these proofs was conducted using the Isabelle/HOL proof assistant.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202508.0891.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202508_0891_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hahn, Kirk, \"Collatz Conjecture Is True for All Positive Integers\", DOI:10.20944/preprints202508.0891.v1 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_20944_preprints202508_0891_v1
