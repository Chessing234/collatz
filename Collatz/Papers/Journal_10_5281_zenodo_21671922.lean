import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kavalenka, Aleh, "Topological transformations in generalized, non-classical Collatz trees", 2026.

Title: Topological transformations in generalized, non-classical Collatz trees

Abstract (from harvested metadata, truncated):
This paper investigates an autonomous, parameterized dynamical system defined as areal-valued generalization of Collatz-like graph structures. We analyze the behavior of trajectories as the system parameter K varies. It is formally proven that, upon transitioningfrom system K to the scaled system 2K within the range 2 < K < 4, edge invariance holdsfor exactly every second odd natural-number node c. This discovery enables a valid graphtransformation in which the fundamental tree topology is entirely preserved. A tree K=1.5with an unlimited number of nodes transforms into a K=3.0 tree, which corresponds to theclassical Collatz conjecture 3n+1.Keywords: graph ,tree , Collatz.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21671922
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21671922

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kavalenka, Aleh, \"Topological transformations in generalized, non-classical Collatz trees\", Zenodo, DOI:10.5281/zenodo.21671922 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21671922
