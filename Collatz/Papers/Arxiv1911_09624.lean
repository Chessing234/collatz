import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mario Weitzer, "An introduction to $p$-adic systems: A new kind of number systems inspired by the Collatz $3n+1$ conjecture", arXiv:1911.09624 [2019].

Title: An introduction to $p$-adic systems: A new kind of number systems inspired by the Collatz $3n+1$ conjecture

Abstract (from OpenAlex metadata, truncated):
This article introduces a new kind of number systems on $p$-adic integers which is inspired by the well-known $3n+1$ conjecture of Lothar Collatz. A $p$-adic system is a piecewise function on $\mathbb{Z}_p$ which has branches for all residue classes modulo $p$ and whose dynamics can be used to define digit expansions of $p$-adic integers which respect congruency modulo powers of $p$ and admit a distinctive "block structure". $p$-adic systems generalize several notions related to $p$-adic integers such as permutation polynomials and put them under a common framework, allowing for results and techniques formulated in one setting to be transferred to another. The general framework established by $p$-adic systems also provides more natural versions of the original Collatz conjecture and first results could be achieved in the context. A detailed formal introduction to $p$-adic systems and the

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1911.09624
-/

namespace Collatz.Papers.Arxiv1911_09624

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mario Weitzer, \"An introduction to $p$-adic systems: A new kind of number systems inspired by the Collatz $3n+1$ conjecture\", arXiv:1911.09624 [2019]."

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

end Collatz.Papers.Arxiv1911_09624
