import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Zöbelein, Carolin, "About the proof of the Collatz conjecture", arXiv:1303.2073 [2013].

Title: About the proof of the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
I want to show one possibility to proof the Collatz conjecture, also called 3n+1 conjecture, for any natural number N. For this, I limit my analysis on the direct odd follower of every natural odd number and show the connections between the already by one reached numbers and their followers, to find an recurrence over all ranges [1,N_{i}], to proof the conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1303.2073
-/

namespace Collatz.Papers.Arxiv1303_2073

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Z\u00f6belein, Carolin, \"About the proof of the Collatz conjecture\", arXiv:1303.2073 [2013]."

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

end Collatz.Papers.Arxiv1303_2073
