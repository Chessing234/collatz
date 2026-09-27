import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Frank Emmert‐Streib, "Structural Properties and Complexity of a New Network Class: Collatz Step Graphs", 2013.

Title: Structural Properties and Complexity of a New Network Class: Collatz Step Graphs

Abstract (from harvested metadata, truncated):
In this paper, we introduce a biologically inspired model to generate complex networks. In contrast to many other construction procedures for growing networks introduced so far, our method generates networks from one-dimensional symbol sequences that are related to the so called Collatz problem from number theory. The major purpose of the present paper is, first, to derive a symbol sequence from the Collatz problem, we call the step sequence, and investigate its structural properties. Second, we introduce a construction procedure for growing networks that is based on these step sequences. Third, we investigate the structural properties of this new network class including their finite scaling and asymptotic behavior of their complexity, average shortest path lengths and clustering...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1371/journal.pone.0056461
-/

namespace Collatz.Papers.Journal_10_1371_journal_pone_0056461

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Frank Emmert‐Streib, \"Structural Properties and Complexity of a New Network Class: Collatz Step Graphs\", PLoS ONE, DOI:10.1371/journal.pone.0056461 [2013]."

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

end Collatz.Papers.Journal_10_1371_journal_pone_0056461
