import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "The Collatz Conjecture: A New Perspective from Algebraic Inverse Trees", 2023.

Title: The Collatz Conjecture: A New Perspective from Algebraic Inverse Trees

Abstract (from harvested metadata, truncated):
This paper addresses the Collatz Conjecture, an open question in mathematics that postulates all positive integers will eventually reach one when a pair of specific operations are repeatedly applied. Despite its apparent simplicity, the conjecture lacks a formal proof. To tackle this enigma, we introduce Algebraic Inverse Trees (AITs), data structures that trace inverse operations of the Collatz sequence. This new approach not only elaborates our unique methodology but also sheds light on the underlying complexities of the Collatz Conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202310.0773.v4
-/

namespace Collatz.Papers.Journal_10_20944_preprints202310_0773_v4

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"The Collatz Conjecture: A New Perspective from Algebraic Inverse Trees\", Preprints.org, DOI:10.20944/preprints202310.0773.v4 [2023]."

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

end Collatz.Papers.Journal_10_20944_preprints202310_0773_v4
