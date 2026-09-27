import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Taha Muhammad, "Collatz Sequence Proof Easy Way", 2026.

Title: Collatz Sequence Proof Easy Way

Abstract (from harvested metadata, truncated):
The document proposes an attempted proof of the Collatz Conjecture by asserting that every Collatz sequence ( S(n) ) eventually reaches the loop ({4,2,1}). The author introduces “Taha’s Collatz Fact 1 (TCF1),” which claims that for any starting value ( n \in \mathbb{N}^+ ), the iterative sequence ( S(n) ) shares the same invariant loop ( IS(n) = {4,2,1} ). The text illustrates this with explicit sequences for ( n = 1 ) through ( n = 7 ), each ending in the standard Collatz cycle. The argument then attempts an induction-based extension: assuming ( IS(r) = {4,2,1} ) for all values up to ( r ), the author analyzes the cases ( r+2 ) even and ( r+2 ) odd, concluding that both lead to the same inv...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2026-wg82x-v2
-/

namespace Collatz.Papers.Journal_10_33774_coe_2026_wg82x_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Taha Muhammad, \"Collatz Sequence Proof Easy Way\", DOI:10.33774/coe-2026-wg82x-v2 [2026]."

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

end Collatz.Papers.Journal_10_33774_coe_2026_wg82x_v2
