import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lynn E. Garner, "On the Collatz 3𝑛+1 algorithm", 1981.

Title: On the Collatz 3𝑛+1 algorithm

Abstract (from harvested metadata, truncated):
The number theoretic function s ( n ) = 1 2 n s(n) = \tfrac {1} {2}n if n n is even, s ( n ) = 3 n + 1 s(n) = 3n + 1 if n n is odd, generates for each n n a Collatz sequence { s k ( n ) } k = 0 ∞ \{ {{s^k}(n)} \}_{k = 0}^\infty , s 0 ( n ) = n {s^0}(n) = n , s k ( n ) = s ( s k − 1 ( n ) ) {s^k}(n) = s({s^{k - 1}}(n)) . It is shown that if a Collatz sequence enters a cycle other than the 4 , 2 , 1 , 4 , … 4,2,1,4, \ldots

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1090/s0002-9939-1981-0603593-2
-/

namespace Collatz.Papers.Journal_10_1090_s0002_9939_1981_0603593_2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lynn E. Garner, \"On the Collatz 3𝑛+1 algorithm\", Proceedings of the American Mathematical Society, DOI:10.1090/s0002-9939-1981-0603593-2 [1981]."

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

end Collatz.Papers.Journal_10_1090_s0002_9939_1981_0603593_2
