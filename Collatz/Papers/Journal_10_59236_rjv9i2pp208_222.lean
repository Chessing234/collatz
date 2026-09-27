import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alison Mountz and Amy Tweedy, "Queering Syracuse", 2010.

Title: Queering Syracuse

Abstract (from harvested metadata, truncated):
This paper recounts the experiences of co-teaching a community engaged seminar focused on study of sexuality and space in the city of Syracuse. This geographical focus grounded engagement and provides here a platform from which to address the difficulties of identifying communities organized around diverse, socially constructed identities. The study of sexuality and space prompts a rethinking of how and whether sexuality operates in the city as a situated series of locations or, rather, a series of identities shaping all spaces. The paper explores a semester-long, student-driven discussion concerning queer as a category in relation to the study of sexuality and community. Through discussion...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.59236/rjv9i2pp208-222
-/

namespace Collatz.Papers.Journal_10_59236_rjv9i2pp208_222

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alison Mountz and Amy Tweedy, \"Queering Syracuse\", Reflections: A Journal of Community-Engaged Writing and Rhetoric, DOI:10.59236/rjv9i2pp208-222 [2010]."

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

end Collatz.Papers.Journal_10_59236_rjv9i2pp208_222
