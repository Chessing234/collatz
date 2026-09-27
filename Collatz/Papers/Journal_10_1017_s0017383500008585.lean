import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for E. M Blaiklock, "Tragedy at Syracuse", 1944.

Title: Tragedy at Syracuse

Abstract (from harvested metadata, truncated):
Mr. chips , one might imagine, would be likely to associate bombs with Caesar for the rest of his quiet days. One Latin lesson tied the two together. A young officer in a New Zealand regiment had that thought in mind when he wrote his belated New Year greetings. ‘You will always think of us’, he said, ‘when you open Thucydides VII. Aren't we vain, Mr. Chips?’ There is no vanity about it. It is not only the memory of a very able Greek class which will entangle for ever the Sicilian Expedition with the events of 1941. There are grimmer reasons. Rommel arrived ominously at Tripoli on the day we read of Gylippus’ coming to Syracuse. We backed to Egypt step by step with the first Athenian disaste...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1017/s0017383500008585
-/

namespace Collatz.Papers.Journal_10_1017_s0017383500008585

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "E. M Blaiklock, \"Tragedy at Syracuse\", Greece and Rome, DOI:10.1017/s0017383500008585 [1944]."

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

end Collatz.Papers.Journal_10_1017_s0017383500008585
