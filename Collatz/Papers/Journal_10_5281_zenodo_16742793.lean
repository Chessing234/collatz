import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jihan, Ikhtiar, "Constructive Resolution of the Collatz Conjecture and 3n±1 Generalizations (Lean Formalization)", 2025.

Title: Constructive Resolution of the Collatz Conjecture and 3n±1 Generalizations (Lean Formalization)

Abstract (from harvested metadata, truncated):
This Lean 3 formalization provides a constructive and fully verified resolution to two important open problems in number theory: The classical Collatz Conjecture (3n + 1 problem) Its full generalization for all natural numbers k involving 3n ± 1 type iterations All proofs are mechanically checked using well-founded induction principles within the Lean 3 proof assistant. The approach is fully constructive and does not rely on any classical axioms, heuristics, or unproven assumptions. This record is uploaded with restricted access to preserve authorship priority. A formal peer-reviewed paper will be submitted later. Author: Ikhtiar Department of Climate and Disaster Management Jashore Universi...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.16742793
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_16742793

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jihan, Ikhtiar, \"Constructive Resolution of the Collatz Conjecture and 3n±1 Generalizations (Lean Formalization)\", Zenodo, DOI:10.5281/zenodo.16742793 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_16742793
