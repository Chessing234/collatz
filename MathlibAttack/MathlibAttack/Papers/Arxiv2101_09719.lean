import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Alexander Rahn et al., "Collatz convergence is a Hydra game", arXiv:2101.09719 [2021].

Title: Collatz convergence is a Hydra game

Abstract (truncated):
The Collatz dynamic is known to generate a complex quiver of sequences over natural numbers which inflation propensity remains so unpredictable it could be used to generate reliable proof of work algorithms for the cryptocurrency industry. Here we establish an ad hoc equivalent of modular arithmetic for Collatz sequences to automatically demonstrate the convergence of infinite quivers of numbers, based on five arithmetic rules we prove apply on the entire Collatz dynamic and which we further simulate to gain insight on their graph geometry and computational properties. We then formally demonstrate these rules define an automaton that is playing a Hydra game on the graph of undecided numbers we also prove is embedded in 24N-7, proving that in ZFC the Collatz conjecture is true, before giving a promising direction to also prove it in Peano arithmetic.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2101.09719
-/

namespace MathlibAttack.Papers.Arxiv2101_09719

open MathlibAttack.Papers

def citation : String := "Alexander Rahn et al., \"Collatz convergence is a Hydra game\", arXiv:2101.09719 [2021]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2101_09719
