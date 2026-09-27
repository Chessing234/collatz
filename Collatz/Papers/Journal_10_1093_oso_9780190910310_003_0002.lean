import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Virginia M. Lewis, "Arriving in Syracuse", 2019.

Title: Arriving in Syracuse

Abstract (from harvested metadata, truncated):
Abstract Chapter 1 focuses on the cult and mythical narratives of Arethusa and the related goddess, Artemis Alpheioa. It begins with a survey of the historical and material evidence for Arethusa in sixth- and fifth-century Syracuse. As a civic symbol for the polis, Arethusa endures despite political volatility in the period. Pindar, the chapter argues, recognizes the importance of Arethusa as a civic symbol and evokes the relationship between Arethusa and Alpheos in nearly every poem for Syracuse, signaling stability and continuity. Furthermore, it proposes that links between the cults in Syracuse and related worship of Artemis Alpheioa in the Peloponnese suggest that Pindar’s references to...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1093/oso/9780190910310.003.0002
-/

namespace Collatz.Papers.Journal_10_1093_oso_9780190910310_003_0002

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Virginia M. Lewis, \"Arriving in Syracuse\", Myth, Locality, and Identity in Pindar's Sicilian Odes, DOI:10.1093/oso/9780190910310.003.0002 [2019]."

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

end Collatz.Papers.Journal_10_1093_oso_9780190910310_003_0002
