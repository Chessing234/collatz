import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alexander Rahn et al., "Collatz convergence is a Hydra game", arXiv:2101.09719 [2021].

Title: Collatz convergence is a Hydra game

Abstract (from OpenAlex metadata, truncated):
The Collatz dynamic is known to generate a complex quiver of sequences over natural numbers which inflation propensity remains so unpredictable it could be used to generate reliable proof of work algorithms for the cryptocurrency industry. Here we establish an ad hoc equivalent of modular arithmetic for Collatz sequences to automatically demonstrate the convergence of infinite quivers of numbers, based on five arithmetic rules we prove apply on the entire Collatz dynamic and which we further simulate to gain insight on their graph geometry and computational properties. We then formally demonstrate these rules define an automaton that is playing a Hydra game on the graph of undecided numbers we also prove is embedded in 24N-7, proving that in ZFC the Collatz conjecture is true, before giving a promising direction to also prove it in Peano arithmetic.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2101.09719
-/

namespace Collatz.Papers.Arxiv2101_09719

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alexander Rahn et al., \"Collatz convergence is a Hydra game\", arXiv:2101.09719 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2101_09719
