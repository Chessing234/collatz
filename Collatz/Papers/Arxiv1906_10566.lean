import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Roy Burson, "Integer Representations and Trajectories of the 3x + 1 Problem", arXiv:1906.10566 [2019].

Title: Integer Representations and Trajectories of the 3x + 1 Problem

Abstract (from OpenAlex metadata, truncated):
This paper studies certain trajectories of the Collatz function. I show that if for each odd number $n$, $n\sim 3n+2$ then every positive integer $n \in \mathbb{N}\setminus 2^{\mathbb{N}}$ has the representation $$n=\left(2^{a_{k+1}}-\sum_{i=0}^{k}{2^{a_i}3^{k-i}}\right)/ 3^{k+1}$$ where $0\le a_0 \le a_1 \le \cdot \cdot \cdot \le a_{k+1}$. As a consequence, in order to prove Collatz Conjecture I illustrate that it is sufficient to prove $n\sim 3n+2$ for any odd $n\in \mathbb{N}\setminus 2^{\mathbb{N}} $. This is the main result of the paper.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1906.10566
-/

namespace Collatz.Papers.Arxiv1906_10566

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Roy Burson, \"Integer Representations and Trajectories of the 3x + 1 Problem\", arXiv:1906.10566 [2019]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1906_10566
