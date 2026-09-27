import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Agelos Kratimenos, "Proof of the Collatz Conjecture", arXiv:1911.02400 [2019].

Title: Proof of the Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
Collatz Conjecture is one of the most famous, for its simple form, proposed more than eighty years ago. This paper presents a full attempt to prove the affirmative answer to the question proposed by the conjecture. In the first section, we propose a number of definitions utilized later on the proof. In the second section, we discover the formula for a characteristic function. This formula describes the functionality of the paths taken for each number based on the Collatz Sequence. In the last section, we prove that every number will eventually reach 1, using the characteristic function.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1911.02400
-/

namespace Collatz.Papers.Arxiv1911_02400

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Agelos Kratimenos, \"Proof of the Collatz Conjecture\", arXiv:1911.02400 [2019]."

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

end Collatz.Papers.Arxiv1911_02400
