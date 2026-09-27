import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Peter Hines, "From a conjecture of Collatz to Thompson's group F, via a conjunction of Girard", arXiv:2202.04443 [2022].

Title: From a conjecture of Collatz to Thompson's group F, via a conjunction of Girard

Abstract (truncated):
The famous 3x + 1 problem of L. Collatz needs no introduction; however, this paper concerns a lesser-known, but similarly unresolved, precursor problem : the Original Collatz Conjecture, or OCC. We demonstrate that the core arithmetic operator from the OCC, when combined with a conjunction of J.-Y. Girard from his Geometry of Interaction system, leads to a realisation of R. Thompson's group F as congruential functions, in the sense of J. Conway. We also give the underlying category theory that accounts for this, and describe the core operator from the OCC as a canonical coherence isomorphism.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2202.04443
-/

namespace MathlibAttack.Papers.Arxiv2202_04443

open MathlibAttack.Papers

def citation : String := "Peter Hines, \"From a conjecture of Collatz to Thompson's group F, via a conjunction of Girard\", arXiv:2202.04443 [2022]."

/-- Recorded claim shell (logic); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2202_04443
