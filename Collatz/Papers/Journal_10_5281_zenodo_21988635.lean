import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nikolai Arkhipov, "«The Structure of Number Dynamics in the Collatz Problem: Patterns of Growth and Decline»", 2026.

Title: «The Structure of Number Dynamics in the Collatz Problem: Patterns of Growth and Decline»

Abstract (from harvested metadata, truncated):
This work examines the behavior of numbers in the Collatz sequence from the perspective of their internal structure and movement patterns. It explores the idea that the growth and decline of numbers are not random processes, but consist of repeating stages: periods of expansion, reaching a certain structural level, and subsequent reduction. The study focuses on how powers of two determine the duration of growth phases, how individual movement blocks are formed, and how transitions between different states occur. The main goal is to describe the hidden organization within the Collatz sequence and to show that numerical trajectories can be viewed as a system of structured transformations rather than as an arbitrary chain of operations. The work presents an approach based on identifying...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21988635
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21988635

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nikolai Arkhipov, \"«The Structure of Number Dynamics in the Collatz Problem: Patterns of Growth and Decline»\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21988635 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21988635
