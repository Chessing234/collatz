import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "Symbolic Complexity is a Bounded Lever for 2-adic Carry Anti-Concentration in the Accelerated 3x + 1 Map: A Fixed-Magnitude Scaling Study", 2026.

Title: Symbolic Complexity is a Bounded Lever for 2-adic Carry Anti-Concentration in the Accelerated 3x + 1 Map: A Fixed-Magnitude Scaling Study

Abstract (from harvested metadata, truncated):
This technical note studies whether symbolic word complexity can supply the 2-adic carry anti-concentration needed in the author’s Effective Occupation Conjecture framework for the accelerated 3x+13x+13x+1 map. Working with synthetic fixed-magnitude ensembles of valuation words, where both word length LLL and total valuation SSS are held constant, the study isolates complexity from the magnitude channel. The carry CD mod 2mC_D \bmod 2^mCDmod2m is tested for excess collision concentration relative to the uniform distribution. The experiments show that factor complexity is genuinely anti-correlated with 2-adic carry concentration: higher-complexity words spread the carry more than low-complexi...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20977206
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20977206

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"Symbolic Complexity is a Bounded Lever for 2-adic Carry Anti-Concentration in the Accelerated 3x + 1 Map: A Fixed-Magnitude Scaling Study\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20977206 [2026]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_20977206
