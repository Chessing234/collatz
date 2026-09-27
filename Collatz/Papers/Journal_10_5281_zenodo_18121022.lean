import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Krishnaswamy Bharati Gandhi Mohan, "The Hidden Order of the Collatz Problem", 2026.

Title: The Hidden Order of the Collatz Problem

Abstract (from harvested metadata, truncated):
The Collatz map is one of the simplest unsolved problems in mathematics to state and one of the most resistant to global analysis. While its forward iteration appears chaotic and its backward structure exhibits unbounded branching, the dynamics remain governed by explicit local rules. In this paper we develop a complete symbolic framework for the accelerated Collatz map that reorganizes both backward and forward dynamics into finite, reversible, and computable structures. Rather than analyzing numerical trajectories directly, we encode Collatz dynamics using finite symbolic words, canonical representatives, and exact decoding rules. We show that every odd integer admits a unique symbolic predecessor chain terminating at a canonical terminal seed 𝑚0 ≡ 3,9,15 (mod 24). These seeds index...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18121022
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18121022

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Krishnaswamy Bharati Gandhi Mohan, \"The Hidden Order of the Collatz Problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18121022 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18121022
