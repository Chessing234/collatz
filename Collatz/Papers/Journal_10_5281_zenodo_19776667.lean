import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Process Definition of Natural Numbers Derived from Waves: The Collatz Conjecture as an Example Case", 2026.

Title: Process Definition of Natural Numbers Derived from Waves: The Collatz Conjecture as an Example Case

Abstract (from harvested metadata, truncated):
Traditional definitions of natural numbers based on Peano axioms rely on "Static Pickups" (extractive axiomatics), which possess a fundamental limitation: according to the Löwenheim–Skolem Theorem, the emergence of non-standard natural numbers ("ghost numbers") remains structurally possible. Within this static framework, dynamic processes such as the Collatz conjecture are inevitably reduced to the halting problem, restricting research to the mere accumulation of empirical data. This paper proposes a fundamental shift from static pickups to a "dynamic process definition" by integrating the concept of "waves as the cause of binary results" (a causal determination process through superposition...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19776667
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19776667

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Process Definition of Natural Numbers Derived from Waves: The Collatz Conjecture as an Example Case\", Zenodo, DOI:10.5281/zenodo.19776667 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19776667
