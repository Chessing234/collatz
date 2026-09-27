import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sebastien Riche, "3X+1 cycles having length k=⌈i log_2(3)⌉", 2026.

Title: 3X+1 cycles having length k=⌈i log_2(3)⌉

Abstract (from harvested metadata, truncated):
A "3x+1" cycle of length k occurs when the Collatz function T(n), which takes odd integers n to (3n+1)/2 and even integers n to n/2, applied to an initial integer a0, reach that initial value again after k iterations, so that T^(k)(a0)= a0. It is conjectured that any positive integer cycle must have k=⌈i log_2(3)⌉ where i is the number of odd elements in the cycle. It is easy to show that in cycles where a0 is the smallest integer, i<3a0 implies k=⌈i log_2(3)⌉. This paper will show that in positive integer cycles, i<304a0 implies k=⌈i log_2(3)⌉. In m-cycles, m<1.8296017a0 implies k=⌈i log_2(3)⌉.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2026-6tt9p-v2
-/

namespace Collatz.Papers.Journal_10_33774_coe_2026_6tt9p_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sebastien Riche, \"3X+1 cycles having length k=⌈i log_2(3)⌉\", DOI:10.33774/coe-2026-6tt9p-v2 [2026]."

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

end Collatz.Papers.Journal_10_33774_coe_2026_6tt9p_v2
