import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ueoka, Yoshiki et al., "A Finite-Peeling Proof of the Collatz Conjecture via the Directed ABN Baumkuchen Representation", 2026.

Title: A Finite-Peeling Proof of the Collatz Conjecture via the Directed ABN Baumkuchen Representation

Abstract (from harvested metadata, truncated):
This paper uses alternating binary notation (ABN) and Collatz phase expression (CPE) to describe the accelerated Collatz map on positive odd integers as an operation on finite words, and formulates an ``ABN Baumkuchen representation'' that transfers this operation to a finite sequence of directed reserved rings. Ordinary ABN zero digits, unused reserved positions, and a special symbol marking a ring cut are separated as distinct types. The special cut is not a numerical digit; it only marks the connection through which the displayed upper carry line is routed to the unique virtual $+1$ input at the inlet of the active lowest ring. The initial canonical ABN is wound onto a single active lowest ring, with finitely many empty reserved rings placed above it. Only the lowest ring receives the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20968007
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20968007

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ueoka, Yoshiki et al., \"A Finite-Peeling Proof of the Collatz Conjecture via the Directed ABN Baumkuchen Representation\", DOI:10.5281/zenodo.20968007 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20968007
