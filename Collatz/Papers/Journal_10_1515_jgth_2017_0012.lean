import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Stefan Kohl, "The Collatz conjecture in a group theoretic context", 2017.

Title: The Collatz conjecture in a group theoretic context

Abstract (from harvested metadata, truncated):
Abstract In this paper we exhibit a permutation group which acts transitively on ℕ 0 {\mathbb{N}_{0}} if and only if the Collatz conjecture holds. We also give an infinite series of finitely generated simple groups many of which contain this group as a subgroup, and whose intersection is isomorphic to Thompson’s group V.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1515/jgth-2017-0012
-/

namespace Collatz.Papers.Journal_10_1515_jgth_2017_0012

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Stefan Kohl, \"The Collatz conjecture in a group theoretic context\", Journal of Group Theory, DOI:10.1515/jgth-2017-0012 [2017]."

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

end Collatz.Papers.Journal_10_1515_jgth_2017_0012
