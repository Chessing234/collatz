import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Konstantin Borovkov and Dietmar Pfeifer, "Estimates for the Syracuse Problem via a Probabilistic Model", 2001.

Title: Estimates for the Syracuse Problem via a Probabilistic Model

Abstract (from harvested metadata, truncated):
We employ a simple stochastic model for the Syracuse problem (also known as the 3x+1 problem) to get estimates for the average behavior of the trajectories of the original deterministic dynamical system. The use of the model is supported not only by certain similarities between the governing rules in the systems, but also by a qualitative estimate of the rate of approximation. From the model, we derive explicit formulae for the asymptotic densities of some sets of interest for the original sequence. We also approximate the asymptotic distributions for the stopping times (times until absorption in the only known cycle {1,2}) of the original system and give numerical illustrations of our results.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1137/s0040585x97978245
-/

namespace Collatz.Papers.Journal_10_1137_s0040585x97978245

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Konstantin Borovkov and Dietmar Pfeifer, \"Estimates for the Syracuse Problem via a Probabilistic Model\", Theory of Probability and Its Applications, DOI:10.1137/s0040585x97978245 [2001]."

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

end Collatz.Papers.Journal_10_1137_s0040585x97978245
