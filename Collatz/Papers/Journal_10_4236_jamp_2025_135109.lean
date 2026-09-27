import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Emilio A. Diarte-Carot, "Solving the Collatz Conjecture, Using Gaussian Arithmetic", 2025.

Title: Solving the Collatz Conjecture, Using Gaussian Arithmetic

Abstract (from harvested metadata, truncated):
We prove that the Collatz, 3n+1 , conjecture is true. To prove this statement, we will first see that, if a number n starts a sequence that satisfies the Collatz conjecture then all sequences containing that number n satisfy the conjecture. We will call these sequences Collatz trajectories. Then, we will study trajectories over equivalence classes defined by the congruences modulo 6, which were already discussed by Carl F. Gauss in 1798, and we will show that all Collatz trajectories contain some number belonging to the class [ 4 ] 6 . Finally, we will prove that all numbers belonging to class [ 4 ] 6 initiate trajectories that satisfy the conjecture. All this proves the first statement: The Collatz conjecture is true.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/jamp.2025.135109
-/

namespace Collatz.Papers.Journal_10_4236_jamp_2025_135109

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Emilio A. Diarte-Carot, \"Solving the Collatz Conjecture, Using Gaussian Arithmetic\", Journal of Applied Mathematics and Physics, DOI:10.4236/jamp.2025.135109 [2025]."

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

end Collatz.Papers.Journal_10_4236_jamp_2025_135109
