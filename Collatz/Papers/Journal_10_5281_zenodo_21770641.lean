import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for yang, taonuo, "A Discrete Dissipative Framework for the Collatz Conjecture: Mod-8 State Machine, Bit-Width Scissors Gap, and a Four-Stage Evolution Model", 2026.

Title: A Discrete Dissipative Framework for the Collatz Conjecture: Mod-8 State Machine, Bit-Width Scissors Gap, and a Four-Stage Evolution Model

Abstract (from harvested metadata, truncated):
Abstract:We integrate three rounds of derivations into a unified framework for analyzing the Collatz conjecture. The framework consists of five layers: a mod-8 state machine fully determining the peeling count; a bit-width potential proving the global expected drift is negative; a scissors-gap inequality ensuring surges of length L >= 3 are net-cancelled; and a logical clipper revealing that any divergent orbit, if it exists, must uniquely correspond to the 2-adic singular point -1 excluded from positive integers. We propose a four-stage discrete dissipative model and honestly list three open problems for future rigorization. Keywords:Collatz conjecture odd-core transform 2-adic valuation dy...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21770641
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21770641

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "yang, taonuo, \"A Discrete Dissipative Framework for the Collatz Conjecture: Mod-8 State Machine, Bit-Width Scissors Gap, and a Four-Stage Evolution Model\", Zenodo, DOI:10.5281/zenodo.21770641 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_21770641
