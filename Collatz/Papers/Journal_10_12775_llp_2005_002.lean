import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jean Paul Van Bendegem, "The Collatz conjecture. A case study in mathematical problem solving", 2005.

Title: The Collatz conjecture. A case study in mathematical problem solving

Abstract (from harvested metadata, truncated):
In previous papers (see Van Bendegem [1993], [1996], [1998], [2000], [2004], [2005], and jointly with Van Kerkhove [2005]) we have proposed the idea that, if we look at what mathematicians do in their daily work, one will find that conceiving and writing down proofs does not fully capture their activity. In other words, it is of course true that mathematicians spend lots of time proving theorems, but at the same time they also spend lots of time preparing the ground, if you like, to construct a proof.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.12775/llp.2005.002
-/

namespace Collatz.Papers.Journal_10_12775_llp_2005_002

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jean Paul Van Bendegem, \"The Collatz conjecture. A case study in mathematical problem solving\", Logic and Logical Philosophy, DOI:10.12775/llp.2005.002 [2005]."

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

end Collatz.Papers.Journal_10_12775_llp_2005_002
