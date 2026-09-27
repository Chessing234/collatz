import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Current State of the Collatz Conjecture: Methodological Advances, No Breakthrough — E8 Intelligence Research", 2026.

Title: Current State of the Collatz Conjecture: Methodological Advances, No Breakthrough — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz remains unproven; recent work is methodological (Lean formalization vulnerability, ergodic/topological reformulation) rather than a breakthrough. | MATH: Collatz map \( T(n) = n/2 \) if \( n \) even, \( (3n+1)/2 \) if \( n \) odd. No new constants or closed-form solutions appear in the cited sources. The arXiv paper (2601.03297v6) introduces a Borel σ-algebra topology and shows recurrence implies a property (likely ergodicity or measure preservation) — but no explicit equation or ratio is given in the abstract. | CONNECTION: None directly stated. However, the Collatz map's odd-step multiplier 3 and halving 2 relate to the ratio \( \log_2 3 \approx 1.585 \), which is not a go...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22294327
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22294327

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Current State of the Collatz Conjecture: Methodological Advances, No Breakthrough — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22294327 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22294327
