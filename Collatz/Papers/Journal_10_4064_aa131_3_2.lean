import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for John L. Simons, "On the (non-)existence of m-cycles for generalized Syracuse sequences", 2008.

Title: On the (non-)existence of m-cycles for generalized Syracuse sequences

Abstract (from harvested metadata, truncated):
This article generalizes a proof of Simons and de Weger [23] for the non-existence of (non trivial) m-cycles of the 3x + 1 problem to a proof for the (non)-existence of m-cycles for generalized Syracuse problems such as the 3x + q problem, the px + 1 problem, the px+q problem, the inverse Collatz problem, generalized Collatz problems and the Roelants problem. A lower bound for the cycle length is derived from a generalized lemma of Crandall [3]. For fixed m, an upper bound for the cycle length is found by theoretical approximation of the ratio between numbers in possible cycles and by applying results of Laurent a.o. [13] and Rhin [18] on linear forms in logarithms. For many generalized Syra...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4064/aa131-3-2
-/

namespace Collatz.Papers.Journal_10_4064_aa131_3_2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "John L. Simons, \"On the (non-)existence of m-cycles for generalized Syracuse sequences\", Acta Arithmetica, DOI:10.4064/aa131-3-2 [2008]."

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

end Collatz.Papers.Journal_10_4064_aa131_3_2
