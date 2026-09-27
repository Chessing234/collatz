import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vincent Fleckinger and Ibrahim Abdoulkarim, "Sur la conjecture de Collatz", arXiv:1607.02370 [2016].

Title: Sur la conjecture de Collatz

Abstract (from OpenAlex metadata, truncated):
We give a generalization of Collatz conjecture or 3n+1 problem on 2-adic completion of Q. A isometric of $Q_2$ provides information on the average behavior of the firsts terms of the sequence according to the class of $u_0$ modulo $2^m$. A generalisation from the pair (2,3) to the pair (p,q) seems possible under the assumption $q^{p-1}

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1607.02370
-/

namespace Collatz.Papers.Arxiv1607_02370

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vincent Fleckinger and Ibrahim Abdoulkarim, \"Sur la conjecture de Collatz\", arXiv:1607.02370 [2016]."

/-- Recorded claim shell (generalization); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1607_02370
