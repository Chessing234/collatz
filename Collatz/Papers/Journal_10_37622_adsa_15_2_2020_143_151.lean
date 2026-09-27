import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fernando Mejias et al., "A Topological Path to the Collatz Conjecture: A historical point of view", 2020.

Title: A Topological Path to the Collatz Conjecture: A historical point of view

Abstract (from harvested metadata, truncated):
In this paper a recent topological approach to the Collatz conjecture is shown.Also known as "the 3x + 1 problem", the Collatz conjecture establishes that for every natural number n, there exists a natural number r such that the r-fold composite κ r (n) = 1, where κ : N → N is the function defined as x/2 if x is even and as 3x + 1 if x is odd.This map κ induces the so called primal topology τ κ on N. We prove that the space (N, τ κ ) is path-connected and compact if and only if the Collatz conjecture is true.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.37622/adsa/15.2.2020.143-151
-/

namespace Collatz.Papers.Journal_10_37622_adsa_15_2_2020_143_151

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fernando Mejias et al., \"A Topological Path to the Collatz Conjecture: A historical point of view\", Advances in Dynamical Systems and Applications, DOI:10.37622/adsa/15.2.2020.143-151 [2020]."

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

end Collatz.Papers.Journal_10_37622_adsa_15_2_2020_143_151
