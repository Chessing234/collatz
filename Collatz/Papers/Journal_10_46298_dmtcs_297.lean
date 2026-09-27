import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Monks, Kenneth G., "3x+1 Minus the +", 2002.

Title: 3x+1 Minus the +

Abstract (from harvested metadata, truncated):
We use Conway's \emphFractran language to derive a function R:\textbfZ^+ → \textbfZ^+ of the form R(n) = r_in if n ≡ i \bmod d where d is a positive integer, 0 ≤ i &lt; d and r_0,r_1, ... r_d-1 are rational numbers, such that the famous 3x+1 conjecture holds if and only if the R-orbit of 2^n contains 2 for all positive integers n. We then show that the R-orbit of an arbitrary positive integer is a constant multiple of an orbit that contains a power of 2. Finally we apply our main result to show that any cycle \ x_0, ... ,x_m-1 \ of positive integers for the 3x+1 function must satisfy \par ∑ _i∈ \textbfE \lfloor x_i/2 \rfloor = ∑ _i∈ \textbfO \lfloor x_i/2 \rfloor +k. \par where \textbfO=\ i : x_i is odd \ , \textbfE=\ i : x_i is even \ , and k=|\textbfO|. \par The method used illustrates...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.46298/dmtcs.297
-/

namespace Collatz.Papers.Journal_10_46298_dmtcs_297

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Monks, Kenneth G., \"3x+1 Minus the +\", Discrete Mathematics & Theoretical Computer Science, DOI:10.46298/dmtcs.297 [2002]."

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

end Collatz.Papers.Journal_10_46298_dmtcs_297
