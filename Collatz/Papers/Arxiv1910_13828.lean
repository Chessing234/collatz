import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Theophilus Agama, "The Theory of the Collatz Process", arXiv:1910.13828 [2019].

Title: The Theory of the Collatz Process

Abstract (from OpenAlex metadata, truncated):
In this paper we introduce and develop the theory of the Collatz process. We leverage this theory to study the Collatz conjecture. This theory also has a subtle connection with the infamous problem of the distribution of Sophie germain primes. We also provide several formulation of the Collatz conjecture in this language.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1910.13828
-/

namespace Collatz.Papers.Arxiv1910_13828

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Theophilus Agama, \"The Theory of the Collatz Process\", arXiv:1910.13828 [2019]."

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

end Collatz.Papers.Arxiv1910_13828
