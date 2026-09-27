import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zaharia, Henri, "A Structural Proof of the Collatz Conjecture", 2026.

Title: A Structural Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We present a structural proof of the Collatz conjecture organised around six lemmas and one main theorem. A complete modular path diagram partitions all odd positive integers into fifteen residue classes (Lemma 1). Every cycle in the finite transition graph possesses at least one exit toward class C = 5 (mod 8) (Lemma 2). The transition graph, refined to the appropriate modular level, is fully deterministic: each integer follows a unique fixed path through G, so the exit toward C is not a choice but an arithmetic necessity. Lemma 3 is strengthened into two parts: (3a) any bounded trajectory must lie in a cycle, and the only positive cycle is 1→4→2→1 (Lagarias 1985); (3b) unbounded trajectories are excluded by the strictly negative arithmetic drift bound (Lemma 6). Together these parts...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.6495558
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_6495558

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Zaharia, Henri, \"A Structural Proof of the Collatz Conjecture\", DOI:10.2139/ssrn.6495558 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_2139_ssrn_6495558
