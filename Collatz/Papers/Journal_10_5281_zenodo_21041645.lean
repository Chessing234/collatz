import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nikolai Arkhipov, "A Complete Proof of the Collatz Conjecture, a General Theory of 3n+d Systems, and the Principle of Minimal Stability", 2026.

Title: A Complete Proof of the Collatz Conjecture, a General Theory of 3n+d Systems, and the Principle of Minimal Stability

Abstract (from harvested metadata, truncated):
This paper presents a complete proof of the Collatz conjecture (3n+1 problem) based on identifying overlapping "proper quadruples" of numbers within sequences that follow the operation pattern x → x/2 → 3(x/2)+1 → n. It is proved that each such quadruple obeys the quadratic equation 3x² − 4x − 4 = 0, whose unique positive root (x = 2) corresponds to the limit cycle 4 → 2 → 1. A complete analysis of the trajectory of the number 27 is performed, identifying all 27 proper quadruples. The uniqueness of the additive constant +1 is demonstrated: the only constants that operate on the same principle are numbers of the form 111...1 with lengths 1, 4, 7, 10... (1 + 3k). The nearest such constant after 1 is 1111. A full analysis of the 3n+1111 cycle for the number 43 is carried out: the cycle...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21041645
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21041645

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nikolai Arkhipov, \"A Complete Proof of the Collatz Conjecture, a General Theory of 3n+d Systems, and the Principle of Minimal Stability\", DOI:10.5281/zenodo.21041645 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21041645
