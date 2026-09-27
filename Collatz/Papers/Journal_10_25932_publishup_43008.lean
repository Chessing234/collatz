import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eldar Sultanow et al., "Collatz Sequences in the Light of Graph Theory", 2019.

Title: Collatz Sequences in the Light of Graph Theory

Abstract (from harvested metadata, truncated):
The Collatz conjecture is a number theoretical problem, which has puzzled countless researchers using myriad approaches. Presently, there are scarcely any methodologies to describe and treat the problem from the perspective of the Algebraic Theory of Automata. Such an approach is promising with respect to facilitating the comprehension of the Collatz sequences "mechanics". The systematic technique of a state machine is both simpler and can fully be described by the use of algebraic means. The current gap in research forms the motivation behind the present contribution. The present authors are convinced that exploring the Collatz conjecture in an algebraic manner, relying on findings and fundamentals of Graph Theory and Automata Theory, will simplify the problem as a whole.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.25932/publishup-43008
-/

namespace Collatz.Papers.Journal_10_25932_publishup_43008

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eldar Sultanow et al., \"Collatz Sequences in the Light of Graph Theory\", publish.UP (University of Potsdam), DOI:10.25932/publishup-43008 [2019]."

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

end Collatz.Papers.Journal_10_25932_publishup_43008
