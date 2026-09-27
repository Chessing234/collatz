import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Benjamin T. Hendel and Rafael O. Ruggiero, "Noncommutativity in the analysis of piecewise discrete-time dynamical systems", arXiv:2306.00712 [2023].

Title: Noncommutativity in the analysis of piecewise discrete-time dynamical systems

Abstract (from OpenAlex metadata, truncated):
In this paper, we present a new method for the analysis of piecewise dynamical systems that are similar to the Collatz conjecture in regard to certain properties of the commutator of their sub-functions. We use the fact that the commutator of polynomials $E(n)=n/2$ and $O(n)=(3n+1)/2$ is constant to study rearrangements of compositions of $E(n)$ and $O(n)$. Our main result is that for any positive rational number $n$, if $(E^{e_1} \circ O^{o_1} \circ E^{e_2} \circ \dotsb \circ O^{o_l} \circ E^{e_{l+1}})(n)=1$, then $(E^{e_1} \circ O^{o_1} \circ E^{e_2} \circ \dotsb \circ O^{o_l} \circ E^{e_{l+1}})(n) = \lceil(E^{e_1 + \dotsb + e_{l+1}} \circ O^{o_1 + \dotsb + o_{l}})(n)\rceil$, where exponentiation is used to denote repeated composition and $e_i$ and $o_i$ are positive integers. Composition sequences of this form have significance in the context of the Collatz conjecture. The techniques 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2306.00712
-/

namespace Collatz.Papers.Arxiv2306_00712

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Benjamin T. Hendel and Rafael O. Ruggiero, \"Noncommutativity in the analysis of piecewise discrete-time dynamical systems\", arXiv:2306.00712 [2023]."

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

end Collatz.Papers.Arxiv2306_00712
