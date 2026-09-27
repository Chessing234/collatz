import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tan, Shan-Guang, "On the solution of the Collatz problem", arXiv:1110.3465 [2011].

Title: On the solution of the Collatz problem

Abstract (from arXiv metadata, truncated):
In this paper, we first prove that given a nonnegative integer $m$ and an odd number $t$ not divisible by $3$, there exists a unique Collatz's Sequence \[ S_{c}(m,t)=\{n_{0}(m,t),n_{1}(m,t),n_{2}(m,t),\ldots,n_{m}(m,t),n_{m+1}(m,t)\} \] produced by a function $n_{i+1}(m,t)=(3n_{i}(m,t)+1)/2$ for $i=0,1,2,\ldots,m$ and ended by an even number $n_{m+1}(m,t)$ where $n_{i}(m,t)=2^{m+1-i}\times3^{i}t-1$ for $i=0,1,2,\ldots,m+1$, by which all odd numbers can be expressed.
  Then we discuss the Collatz problem in two ways and prove that each Collatz's Sequence always returns to 1, i.e., the Collatz problem is solved.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1110.3465
-/

namespace Collatz.Papers.Arxiv1110_3465

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tan, Shan-Guang, \"On the solution of the Collatz problem\", arXiv:1110.3465 [2011]."

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

end Collatz.Papers.Arxiv1110_3465
