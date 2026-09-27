import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Matt Hohertz and Bahman Kalantari, "Collatz polynomials: an introduction with bounds on their zeros", arXiv:2001.00482 [2019].

Title: Collatz polynomials: an introduction with bounds on their zeros

Abstract (from OpenAlex metadata, truncated):
The Collatz Conjecture (also known as the 3x+1 Problem) proposes that the following algorithm will, after a certain number of iterations, always yield the number 1: given a natural number, multiply by three and add one if the number is odd, halve the resulting number, then repeat. In this article, for each $N$ for which the Collatz Conjecture holds we define the $N^{th}$ Collatz polynomial to be the monic polynomial with constant term $N$ and $k^{th}$ term (for $k > 1$) the $k^{th}$ iterate of $N$ under the Collatz function. In particular, we bound the moduli of the roots of these polynomials, prove theorems on when they have rational integer roots, and suggest further applications and avenues of research.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2001.00482
-/

namespace Collatz.Papers.Arxiv2001_00482

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Matt Hohertz and Bahman Kalantari, \"Collatz polynomials: an introduction with bounds on their zeros\", arXiv:2001.00482 [2019]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2001_00482
