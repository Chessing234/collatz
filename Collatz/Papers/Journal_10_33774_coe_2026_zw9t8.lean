import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for MOTIMBA, Dylan, "All orbits of the collatz map attain the trivial cycle 4 2 1: A proof via the theory of huts and 2-adic classification classes", 2026.

Title: All orbits of the collatz map attain the trivial cycle 4 2 1: A proof via the theory of huts and 2-adic classification classes

Abstract (from harvested metadata, truncated):
We present a complete proof of the Collatz conjecture. We transport Syracuse orbits by multiplying every odd term by three. The evolution then depends only on the local 2-adic valuations of the two neighboring even multiples of six. To formalize this we introduce huts, equivalence classes of odd multiples of three defined by the pair of valuations of their borders. For the factor three only three families exist: the base hut, huts of type one-alpha, and huts of type alpha-one. Ordered by the sum of minimal representatives, the set of huts is well-ordered, allowing strong induction. We classify the Collatz transformation on huts. A hut of type one-alpha always moves to the strictly smaller hut one-(alpha minus one). A hut of type alpha-one moves either to a hut of type one-beta or to a hut...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2026-zw9t8
-/

namespace Collatz.Papers.Journal_10_33774_coe_2026_zw9t8

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "MOTIMBA, Dylan, \"All orbits of the collatz map attain the trivial cycle 4 2 1: A proof via the theory of huts and 2-adic classification classes\", DOI:10.33774/coe-2026-zw9t8 [2026]."

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

end Collatz.Papers.Journal_10_33774_coe_2026_zw9t8
