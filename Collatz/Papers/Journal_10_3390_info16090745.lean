import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Mailland and Iwona Grobelna, "A Novel Approach to the Collatz Conjecture with Petri Nets", 2025.

Title: A Novel Approach to the Collatz Conjecture with Petri Nets

Abstract (from harvested metadata, truncated):
The Collatz conjecture is a famous unsolved problem in mathematics, known for its deceptively simple rules that generate complex, unpredictable behaviour. It can be efficiently modelled using a Petri net that represents its inverse graph, where each place corresponds to an integer and each transition encodes an inverse rule. The net, constructed up to a bound n, reveals the tree-like structure of predecessors and highlights properties such as recurrence, reachability, and liveness. Token flows simulate possible trajectories towards 1. This formal approach enables the investigation of the problem through discrete event systems theory and opens perspectives for parametric or inductive extensions beyond the bounded domain. The model proposed provides a structured framework for visualising...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/info16090745
-/

namespace Collatz.Papers.Journal_10_3390_info16090745

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Mailland and Iwona Grobelna, \"A Novel Approach to the Collatz Conjecture with Petri Nets\", Information, DOI:10.3390/info16090745 [2025]."

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

end Collatz.Papers.Journal_10_3390_info16090745
