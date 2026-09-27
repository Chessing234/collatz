import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture Remains Unsolved: Statistical Growth Below Unity — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Remains Unsolved: Statistical Growth Below Unity — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The dominant unsolved problem surfaced is the Collatz Conjecture (3n+1), not a new competition result; the other hits are generic olympiad/entertainment content. | MATH: Collatz map: \( T(n) = n/2 \) if \( n \) even, \( T(n) = 3n+1 \) if \( n \) odd. Conjecture: \( \forall n \in \mathbb{N}, \exists k: T^k(n) = 1 \). No closed-form solution; known statistical behavior: average growth factor per step \( \approx (1/2)^{1/2} \cdot (3/2)^{1/2} = \sqrt{3/4} \approx 0.866 < 1 \), implying logarithmic drift toward 1. | CONNECTION: The ratio \( \sqrt{3/4} = 0.866 \) is not a golden-ratio harmonic, but the structure of the Collatz tree exhibits self-similarity and a binary/ternary branching p...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22268850
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22268850

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture Remains Unsolved: Statistical Growth Below Unity — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22268850 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22268850
