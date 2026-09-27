import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kosobutskyy, Petro, "The Jacobsthal-Collatz-Terras model of conjecture the natural numbers in &lt;i&gt;κq&lt;/i&gt; + 1 problems", 2025.

Title: The Jacobsthal-Collatz-Terras model of conjecture the natural numbers in &lt;i&gt;κq&lt;/i&gt; + 1 problems

Abstract (from harvested metadata, truncated):
In the work, the unity of the model in both directions of the change of the power of two of the conjecture of natural numbers structured in the form of a set parametrized by a set of odd θ sequences θ × 2 n is justified for the first time. It is shown that the graphs of the direct n(tst) → ∞ and reverse n → 0 conjecture of numbers are correctly displayed by the branching diagram of the sequences oriented along the time axis of the full stop of Terrase. The distance between neighbouring nodes is shown to correlate with the Collatz function. The distance δm(p), κ = ακCκq±1 between adjacent nodes is shown to be correlated with the Collatz function. The obtained formula for calculating the period Tκ = ln2(1 + ακκ) according to the degree of formation of powers n. Based on the analysis of...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.59400/jam1767
-/

namespace Collatz.Papers.Journal_10_59400_jam1767

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kosobutskyy, Petro, \"The Jacobsthal-Collatz-Terras model of conjecture the natural numbers in &lt;i&gt;κq&lt;/i&gt; + 1 problems\", Journal of AppliedMath, DOI:10.59400/jam1767 [2025]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_59400_jam1767
