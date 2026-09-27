import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fortunado, Ismael Tabuñar, "Proof of Collatz Conjecture: The Traps, a Flowchart, Their IDs (Number Identification), a Table or Summary, Collatz Conjecture Inequality and Analysis", 2022.

Title: Proof of Collatz Conjecture: The Traps, a Flowchart, Their IDs (Number Identification), a Table or Summary, Collatz Conjecture Inequality and Analysis

Abstract (from harvested metadata, truncated):
Abstract: The author used steps to show that all number using 3n + 1 conjecture will fall to 4, 2 and eventually 1. And that only one cycle exists. The positive integers may lie to patterns. These could be called traps. A flowchart was used. Each number will have a particular ID dictated by the flowchart. Then an analysis explaining that it ends in 1 and only having one cycle – the 4, 2 and 1 cycle. The number could reach “infinity” but still has a tail. Keywords: Collatz conjecture, Flowchart, Generalized Collatz Conjecture, Identification, Inequality. Title: Proof of Collatz Conjecture: The Traps, a Flowchart, Their IDs (Number Identification), a Table or Summary, Collatz Conjecture Inequa...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.6856708
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_6856708

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fortunado, Ismael Tabuñar, \"Proof of Collatz Conjecture: The Traps, a Flowchart, Their IDs (Number Identification), a Table or Summary, Collatz Conjecture Inequality and Analysis\", Zenodo, DOI:10.5281/zenodo.6856708 [2022]."

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

end Collatz.Papers.Journal_10_5281_zenodo_6856708
