import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yoshihito Matsuura, "Why the Collatz Problem Was Considered "Out of Reach": A Structural Perspective on a Long-Standing Assessment", 2026.

Title: Why the Collatz Problem Was Considered "Out of Reach": A Structural Perspective on a Long-Standing Assessment

Abstract (from harvested metadata, truncated):
The Collatz problem has long been regarded as a paradigmatic example of a simple-to-state question that resists resolution. This perception is often encapsulated in the remark attributed to Paul Erdős that “mathematics is not yet ready for such problems,” a sentiment later reiterated and contextualized in surveys by Jeffrey Lagarias. While frequently quoted, this assessment is rarely examined as a substantive diagnosis of what, precisely, was considered lacking in existing mathematical approaches. This paper offers a historical and methodological interpretation of that assessment. Drawing on the survey literature, it argues that the enduring difficulty of the Collatz problem has been consistently associated with identifiable structural obstacles: the absence of effective monotone...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18122718
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18122718

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yoshihito Matsuura, \"Why the Collatz Problem Was Considered \"Out of Reach\": A Structural Perspective on a Long-Standing Assessment\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18122718 [2026]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_18122718
