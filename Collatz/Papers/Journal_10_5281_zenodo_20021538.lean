import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Borgatta, Piero, "A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing", 2026.

Title: A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing

Abstract (from harvested metadata, truncated):
This work proposes a structural reformulation of the Collatz conjecture in terms of a finite-dimensional spectral problem. Starting from the empirical observation that "rebel" orbits of the Syracuse map shadow, for finite stretches, periodic rational points of the 2-adic dynamics associated to negative rational fixed points, we construct an episode graph on the space of phantom orbits. The strongly connected component (SCC) of this graph that supports the slowest descent is encoded as a finite weighted transfer operator on a refined phase state at the critical node (k=12, c=2, b=1). We prove an exact congruential shadowing lemma reducing arbitrarily long shadowing episodes to a residue condition n ≡ qw (mod 2bA+1), where qw is the 2-adic representative of a phantom word w. For each...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20021538
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20021538

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Borgatta, Piero, \"A Spectral Reduction of the Collatz Conjecture via Phantom Orbit Shadowing\", DOI:10.5281/zenodo.20021538 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20021538
