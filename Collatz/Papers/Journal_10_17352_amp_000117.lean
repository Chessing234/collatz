import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ling Xie, "Comment: Paper on the progress of pure mathematics "proof of 3x + 1 conjecture"", 2024.

Title: Comment: Paper on the progress of pure mathematics "proof of 3x + 1 conjecture"

Abstract (from harvested metadata, truncated):
The unresolved problem in number theory: the 3x+1 problem, deeply loved by math enthusiasts. I saw a paper titled "Proof of 3x+1 Conjecture" in the Journal of Pure Mathematical Progress (ISSN Print: 2160-0368), and its proof was incorrect.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17352/amp.000117
-/

namespace Collatz.Papers.Journal_10_17352_amp_000117

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ling Xie, \"Comment: Paper on the progress of pure mathematics \"proof of 3x + 1 conjecture\"\", Annals of Mathematics and Physics, DOI:10.17352/amp.000117 [2024]."

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

end Collatz.Papers.Journal_10_17352_amp_000117
