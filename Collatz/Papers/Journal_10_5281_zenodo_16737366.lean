import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Thaler, Mario Heinrich, "A Universal Drift Invariant and the Resolution of the Collatz Conjecture", 2025.

Title: A Universal Drift Invariant and the Resolution of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
## Experimental Disclosure Notice**This work is part of a documented experiment on AI-generated mathematical content.** The mathematical arguments presented were produced by large language models (primarily ChatGPT) with minimal human intervention, as part of a study examining AI capabilities in formal mathematics and the robustness of academic publication processes.The content should be evaluated critically and is not guaranteed to be mathematically sound. For a full methodological discussion and analysis of this experiment, see:M. H. Thaler, *Proofing Collatz with AI: A Retrospective on an Experimental Publication Process* (2025). DOI: https://doi.org/10.5281/zenodo.17232247**Transparency...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.16737366
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_16737366

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Thaler, Mario Heinrich, \"A Universal Drift Invariant and the Resolution of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.16737366 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_16737366
