import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Everett, Brandon, "The Collatz Conjecture as a Computational Primitive", 2026.

Title: The Collatz Conjecture as a Computational Primitive

Abstract (from harvested metadata, truncated):
This paper reframes the Collatz Conjecture not as an open problem in number theory but as a specimen of a broader computational primitive: iterative arithmetic reduction between incommensurate scales. The two branches of the Collatz map encode a fundamental tension — the even step (÷2) performs digital reduction while the odd step (3n+1) introduces analog complexity at a scale incommensurate with the binary grid. This tension is structurally identical to the Pythagorean comma in music, the successive-approximation architecture of analog-to-digital converters, and the negotiation dynamics between coupled cognitive agents in the Memory as Baseline Deviation (MBD) framework. Four mechanisticall...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20618194
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20618194

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Everett, Brandon, \"The Collatz Conjecture as a Computational Primitive\", Zenodo, DOI:10.5281/zenodo.20618194 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20618194
