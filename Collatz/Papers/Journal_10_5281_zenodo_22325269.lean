import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Unsolved Math Problems: Hadwiger-Nelson, Josephus, Collatz, Odd Perfect Numbers — E8 Intelligence Research", 2026.

Title: Unsolved Math Problems: Hadwiger-Nelson, Josephus, Collatz, Odd Perfect Numbers — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The search results surface four distinct unsolved/classic problems from Numberphile/Veritasium — Hadwiger-Nelson (chromatic number of the plane), Josephus problem, Collatz conjecture, and odd perfect numbers — plus an unrelated omnidirectional video quality paper. | MATH: Hadwiger-Nelson: χ(ℝ²) ∈ {5,6,7} (lower bound 5 via de Grey 2018, upper bound 7 via hexagonal tiling); Josephus: J(n,k) = (J(n−1,k)+k) mod n, closed form J(n,2) = 2l+1 where n = 2^m + l; Collatz: T(n) = n/2 if even, 3n+1 if odd, conjecture ∀n ∃k: T^k(n)=1; odd perfect numbers: σ(N) = 2N, N odd — existence unknown, lower bound N > 10^1500. | CONNECTION: Hadwiger-Nelson upper bound 7 arises from hexagonal tiling — a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22325269
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22325269

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Unsolved Math Problems: Hadwiger-Nelson, Josephus, Collatz, Odd Perfect Numbers — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22325269 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22325269
