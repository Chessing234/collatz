import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Peter Hines, "From a conjecture of Collatz to Thompson's group F, via a conjunction of Girard", arXiv:2202.04443 [2022].

Title: From a conjecture of Collatz to Thompson's group F, via a conjunction of Girard

Abstract (from OpenAlex metadata, truncated):
The famous 3x + 1 problem of L. Collatz needs no introduction; however, this paper concerns a lesser-known, but similarly unresolved, precursor problem : the Original Collatz Conjecture, or OCC. We demonstrate that the core arithmetic operator from the OCC, when combined with a conjunction of J.-Y. Girard from his Geometry of Interaction system, leads to a realisation of R. Thompson's group F as congruential functions, in the sense of J. Conway. We also give the underlying category theory that accounts for this, and describe the core operator from the OCC as a canonical coherence isomorphism.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2202.04443
-/

namespace Collatz.Papers.Arxiv2202_04443

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Peter Hines, \"From a conjecture of Collatz to Thompson's group F, via a conjunction of Girard\", arXiv:2202.04443 [2022]."

/-- Recorded main claim shell (logic); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2202_04443
