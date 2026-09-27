import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Reduced Collatz Dynamics is Periodical and the Period equals 2 to the power of the count of x/2   ", 2020.

Title: Reduced Collatz Dynamics is Periodical and the Period equals 2 to the power of the count of x/2   

Abstract (from harvested metadata, truncated):
We propose Reduced Collatz Conjecture that is equivalent to Collatz Conjecture but is easier to explore, because reduced dynamics is more primitive than original dynamics and presents better structures (e.g., period and ratio). Reduced dynamics (that are occurred computation sequence from a starting integer to the first integer less than the starting integer) is the component of original dynamics (from a starting integer to 1). Reduced dynamics of x is represented by a sequence of computation that is either (3*x+1)/2 or x/2, because 3*x+1 is always even and followed by x/2. We prove that reduced dynamics is periodical and its period equals 2 to the power of the count of x/2. More specificall...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.36227/techrxiv.11664501.v1
-/

namespace Collatz.Papers.Journal_10_36227_techrxiv_11664501_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Reduced Collatz Dynamics is Periodical and the Period equals 2 to the power of the count of x/2   \", DOI:10.36227/techrxiv.11664501.v1 [2020]."

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

end Collatz.Papers.Journal_10_36227_techrxiv_11664501_v1
