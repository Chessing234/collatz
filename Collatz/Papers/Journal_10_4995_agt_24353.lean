import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ángel Guale and Jorge Vielma, "On local semirings induced by topologies: An algebraic approach to the Collatz conjecture", 2026.

Title: On local semirings induced by topologies: An algebraic approach to the Collatz conjecture

Abstract (from harvested metadata, truncated):
We present an algebraic approach to the Collatz conjecture by studying the topology τf on ℕ induced by the Collatz function f, where the open sets θ ⊂ ℕ satisfy f-1 ( θ ) ⊂ θ . This topology, known as \emph{primal topology}, turns τf into a commutative semiring. We prove that the Collatz conjecture holds if and only if τf is local. More generally, we show that any compact primal topology corresponds to a semiring that decomposes as a finite direct sum of certain local semirings and that primal compactness connectedness characterises locality. In addition, we establish that a topological space is not w-R0 if and only if its associated semiring of open sets has a unique maximal ideal such that it is an avoidance ideal of a closed set.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4995/agt.24353
-/

namespace Collatz.Papers.Journal_10_4995_agt_24353

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ángel Guale and Jorge Vielma, \"On local semirings induced by topologies: An algebraic approach to the Collatz conjecture\", Applied General Topology, DOI:10.4995/agt.24353 [2026]."

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

end Collatz.Papers.Journal_10_4995_agt_24353
