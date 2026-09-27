import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ari Arapostathis and Vivek S. Borkar, "`Controlled' versions of the Collatz-Wielandt and Donsker-Varadhan formulae", arXiv:1903.10714 [2019].

Title: `Controlled' versions of the Collatz-Wielandt and Donsker-Varadhan formulae

Abstract (from OpenAlex metadata, truncated):
This is an overview of the work of the authors and their collaborators on the characterization of risk sensitive costs and rewards in terms of an abstract Collatz-Wielandt formula and in case of rewards, also a controlled version of the Donsker-Varadhan formula. For the finite state and action case, this leads to useful linear and dynamic programming formulations in the reducible case.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1903.10714
-/

namespace Collatz.Papers.Arxiv1903_10714

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ari Arapostathis and Vivek S. Borkar, \"`Controlled' versions of the Collatz-Wielandt and Donsker-Varadhan formulae\", arXiv:1903.10714 [2019]."

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

end Collatz.Papers.Arxiv1903_10714
