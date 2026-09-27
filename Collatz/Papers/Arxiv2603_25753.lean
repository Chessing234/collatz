import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Chang, Edward Y., "A Structural Reduction of the Collatz Conjecture to One-Bit Orbit Mixing", arXiv:2603.25753 [2026].

Title: A Structural Reduction of the Collatz Conjecture to One-Bit Orbit Mixing

Abstract (from OpenAlex metadata, truncated):
We reduce the Collatz conjecture to a fixed-modulus, one-bit orbit-mixing problem. Working with the compressed odd-to-odd Collatz map, we prove exact low-depth decomposition formulas at depths K = 3, 4, 5, reducing block-discrepancy terms to explicit run statistics. We then prove a Map Balance Theorem: among the 2^(K-3), 1 burst residues modulo 2^K that initiate gaps, the counts mapping to gap starts congruent to 3 versus congruent to 7 (mod 8) differ by exactly 1 for every K >= 5. Thus all residual bias is orbit-level, not map-level. For the dominant n congruent to 1 (mod 8) class, the gap outcome depends on a single binary variable, bit 4 of the orbit value at burst-ending times, reducing the conjecture to whether every orbit visits two residue classes modulo 32 with sufficient balance along a sparse subsequence.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2603.25753
-/

namespace Collatz.Papers.Arxiv2603_25753

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Chang, Edward Y., \"A Structural Reduction of the Collatz Conjecture to One-Bit Orbit Mixing\", arXiv:2603.25753 [2026]."

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

end Collatz.Papers.Arxiv2603_25753
