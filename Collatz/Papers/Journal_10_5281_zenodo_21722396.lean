import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for huang, yan, "A Rigorous Algebraic Proof of the Collatz Conjecture Based on a  Modulo-8 Type System, Expansion Cycle Fixed Point, and Congruence Constraints", 2026.

Title: A Rigorous Algebraic Proof of the Collatz Conjecture Based on a  Modulo-8 Type System, Expansion Cycle Fixed Point, and Congruence Constraints

Abstract (from harvested metadata, truncated):
This paper presents a rigorous algebraic proof of the Collatz conjecture. The mapping (3X+1)/2(3X+1)/2 is classified into four exhaustive types (2A+1, 2B+1, 2A, 2B) based on modulo-8 residues with deterministic transition rules. The unique expansion cycle F(X)=(27X+19)/16F(X)=(27X+19)/16 has fixed point −19/11∉N+−19/11∈/N+ and admits only finitely many repetitions by a bit-length bound. All odd iterates decompose exhaustively into three segment types (A, B, C). Type C periodic orbits are strictly excluded by the identity Tk=Mk+1+1Tk=Mk+1+1 together with Mk≥2Mk≥2, yielding 2n>(2.25)n2n>(2.25)n. Non-periodic infinite Type C chains are excluded by a congruence fixed-point argument: the accumulated inverse mapping forces the initial odd parameter to equal a strictly changing integer sequence...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21722396
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21722396

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "huang, yan, \"A Rigorous Algebraic Proof of the Collatz Conjecture Based on a  Modulo-8 Type System, Expansion Cycle Fixed Point, and Congruence Constraints\", DOI:10.5281/zenodo.21722396 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_21722396
