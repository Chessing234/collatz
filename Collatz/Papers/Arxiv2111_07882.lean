import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "Functional Equations Associated to Collatz-Type Maps on Integer Rings of Algebraic Number Fields", arXiv:2111.07882 [2021].

Title: Functional Equations Associated to Collatz-Type Maps on Integer Rings of Algebraic Number Fields

Abstract (from OpenAlex metadata, truncated):
In 1995, Meinardus & Berg presented a reformulation of the Collatz Conjecture in terms of a functional equation in a single complex variable over the open unit disk. This paper generalizes that method to deal with not only a large class of Collatz-type maps defined on the integers, but further generalizations thereof to Collatz-type maps on the rings of integers on an arbitrary algebraic number field.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2111.07882
-/

namespace Collatz.Papers.Arxiv2111_07882

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"Functional Equations Associated to Collatz-Type Maps on Integer Rings of Algebraic Number Fields\", arXiv:2111.07882 [2021]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2111_07882
