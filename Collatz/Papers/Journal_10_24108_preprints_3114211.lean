import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Farhad Aliabdali, "Collatz Analysis Two-Stage Tree and Multiset Calculus", 2026.

Title: Collatz Analysis Two-Stage Tree and Multiset Calculus

Abstract (from harvested metadata, truncated):
Collatz Analysis: Two-Stage Tree and Multiset Calculus Farhad Aliabdali Additionally, we develop a signed-multiset calculus on generators {g_j} that encodes binary arithmetic via local rewrite rules. We prove this system is terminating and confluent, yielding unique canonical binary normal forms. Within this calculus, we derive an explicit bit-complement formula for 2^D-3^k and reformulate the classical cycle equation in multiset language, enabling digit-by-digit analysis of cycle constraints. By applying a Multiset Calculus, we derive a polynomial obstruction showing that any cycle's algebraic structure is incompatible with positive-coefficient polynomial division. While this does not stric...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.24108/preprints-3114211
-/

namespace Collatz.Papers.Journal_10_24108_preprints_3114211

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Farhad Aliabdali, \"Collatz Analysis Two-Stage Tree and Multiset Calculus\", DOI:10.24108/preprints-3114211 [2026]."

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

end Collatz.Papers.Journal_10_24108_preprints_3114211
