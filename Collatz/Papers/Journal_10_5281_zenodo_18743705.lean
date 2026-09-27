import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kalhori, Mohammad Reza, "The Proof of the Collatz Conjecture via Reverse Branching Analysis and Tree Incompatibility", 2026.

Title: The Proof of the Collatz Conjecture via Reverse Branching Analysis and Tree Incompatibility

Abstract (from harvested metadata, truncated):
This work presents a complete structural proof of the Collatz Conjecture based on two core mechanisms: Reverse Branching Analysis and Tree Incompatibility. The approach reconstructs the inverse Collatz graph, identifies all admissible and non-admissible branches, and demonstrates that no divergent or non-terminating trajectories can exist. The proof establishes that every positive integer eventually reaches 1 under the standard Collatz iteration. The manuscript includes formal definitions, structural lemmas, and a full logical derivation of the incompatibility of infinite reverse paths. This version is the first public release of the complete proof.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18743705
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18743705

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kalhori, Mohammad Reza, \"The Proof of the Collatz Conjecture via Reverse Branching Analysis and Tree Incompatibility\", Zenodo, DOI:10.5281/zenodo.18743705 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18743705
