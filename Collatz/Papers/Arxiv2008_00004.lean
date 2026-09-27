import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Derek Tucker, "Elegant Proof of the 3n + 1 Problem via Modular Algebra", arXiv:2008.00004 [2020].

Title: Elegant Proof of the 3n + 1 Problem via Modular Algebra

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture is true, the 3n +1 problem generates a fractal spiral from odd multiples of three to elements 5 mod 8, if they are not already, and from there onto smaller elements already known to go to one. If T is the reduced Syracuse function, then if T(u) = x, so too does T(4u+1) = x. Also 3 mod 4 elements inevitabley map to 1 mod 4. All must descend.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2008.00004
-/

namespace Collatz.Papers.Arxiv2008_00004

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Derek Tucker, \"Elegant Proof of the 3n + 1 Problem via Modular Algebra\", arXiv:2008.00004 [2020]."

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

end Collatz.Papers.Arxiv2008_00004
