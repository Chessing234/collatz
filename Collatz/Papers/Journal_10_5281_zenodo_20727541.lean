import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for C. Mike Rubendall, "A DIRECT PROOF OF THE RIEMANN HYPOTHESIS VIA RESIDUE BIJECTION OF THE 2-ADIC NORMALIZED COLLATZ MAP", 2026.

Title: A DIRECT PROOF OF THE RIEMANN HYPOTHESIS VIA RESIDUE BIJECTION OF THE 2-ADIC NORMALIZED COLLATZ MAP

Abstract (from harvested metadata, truncated):
A 2-part proof of the Collatz Conjecture and the Riemann Hypothesis. Abstract. We present a short, elementary proof of the Collatz Conjecture within ZFC. Byintroducing a single-rule iterationf (x) = 3x + 2ν2(x),where ν2(x) denotes the largest exponent n such that 2n | x, we show that the Collatz dynamicsreduce to a successor map that is strictly increasing along each forward orbit (orbitwise injective).Using orbitwise injectivity, residue coverage, and absorption by powers of two, we prove that allnatural numbers eventually reach 1 in finite time. Abstract. We now map the collapsed Collatz Function to the critical strip of the Riemann ZetaFunction to prove the distribution of primes is causally vectored beginning with the construction ofthe critical line under residue projection to the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20727541
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20727541

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "C. Mike Rubendall, \"A DIRECT PROOF OF THE RIEMANN HYPOTHESIS VIA RESIDUE BIJECTION OF THE 2-ADIC NORMALIZED COLLATZ MAP\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20727541 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20727541
