import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wu, Zhenghao, "A Method of Finding All Existing Starting Numbers For Finite Arbitrarily Long Collatz Trajectories That Obey Any Behavior/Dynamics of Our Choosing.", 2026.

Title: A Method of Finding All Existing Starting Numbers For Finite Arbitrarily Long Collatz Trajectories That Obey Any Behavior/Dynamics of Our Choosing.

Abstract (from harvested metadata, truncated):
We provide a general analytic formula to construct all existing starting odd numbers that obey our desired finite arbitrarily long Collatz trajectory, meaning that these starting odd numbers obey our pre-designated maximum factors of 2 at each iteration of the reduced Collatz map. We also provide another general analytic formula for finding the resulting odd numbers after N iterations of the reduced Collatz map. These formulas shed light on the structure of Collatz trajectories and other properties. We can also use this information to find in finite steps all existing Collatz trajectories that become 1 after any finite N iterations.We also will see that the ”location” of all of the 1’s in Collatz Conjecture can be found by solving a special case of the discrete log problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20710317
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20710317

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wu, Zhenghao, \"A Method of Finding All Existing Starting Numbers For Finite Arbitrarily Long Collatz Trajectories That Obey Any Behavior/Dynamics of Our Choosing.\", DOI:10.5281/zenodo.20710317 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20710317
