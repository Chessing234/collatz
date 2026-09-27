import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Reid, Steven, "The Recursive Division Tree and Collatz Conjecture: Independent Measures of Integer Complexity", 2025.

Title: The Recursive Division Tree and Collatz Conjecture: Independent Measures of Integer Complexity

Abstract (from harvested metadata, truncated):
We analyze the relationship between two measures of integer complexity: the Recursive Division Tree (RDT) depth and the Collatz stopping time. Using multi-scale statistical analysis, we show that these measures are fundamentally independent. Although the raw correlation decreases with scale (from approximately r≈0.20r \approx 0.20r≈0.20 for n 5×104n > 5 \times 10^4n>5×104), this effect is entirely spurious. Both measures share a weak dependence on integer size, which creates an artificial correlation in uncontrolled samples. RDT depth exhibits a strong correlation with log⁡n\log nlogn (r=0.76r = 0.76r=0.76), consistent with its doubly logarithmic construction, while Collatz stopping time sho...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17663191
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17663191

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Reid, Steven, \"The Recursive Division Tree and Collatz Conjecture: Independent Measures of Integer Complexity\", Zenodo, DOI:10.5281/zenodo.17663191 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17663191
