import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for DO VAN TRUNG and DO VAN TRUNG, "Proving the Collatz Conjecture: A Weak Lyapunov Model Based on Logarithmic Energy Functions", 2026.

Title: Proving the Collatz Conjecture: A Weak Lyapunov Model Based on Logarithmic Energy Functions

Abstract (from harvested metadata, truncated):
AbstractThe Collatz Conjecture remains one of the most famous open problems inmathematics. Despite its simple definition, a general proof has yet to be established.In this paper, we propose an approach based on dynamical systems modeling byconstructing an Energy Function with average decay properties, incorporating aLemma based on the results of mathematician Terence Tao. We prove that after afinite number of iterations, the system's energy always decreases, identifying it as aweak Lyapunov function for the Collatz system. This direction opens new possibilitiesin connecting number theory with mathematical physics systems such as entropy,thermodynamics, and discrete dynamics. Keywords: Collat...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19971831
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19971831

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "DO VAN TRUNG and DO VAN TRUNG, \"Proving the Collatz Conjecture: A Weak Lyapunov Model Based on Logarithmic Energy Functions\", Zenodo, DOI:10.5281/zenodo.19971831 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19971831
