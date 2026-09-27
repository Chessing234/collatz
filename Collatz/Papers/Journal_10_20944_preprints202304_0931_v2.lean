import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jishe Feng, "Proof the Collatz Conjecture in Binary Strings", 2023.

Title: Proof the Collatz Conjecture in Binary Strings

Abstract (from harvested metadata, truncated):
The following is the Collatz Conjecture: Suppose we begin with a positive number, multiply it by 3 and add 1 if it is odd, and divide it by 2 if it is even. Then continue doing this as long as you can. Will it matter where you start, whether you end up at the number 1? The Collatz conjecture has been studied for around 85 years. We transform the Collatz function from decimal to binary, then use the binary string's character to prove the Collatz conjecture. In addition, we use mathematics to give another interpretation to chaos, which is the ultimately periodic positive integer sequence.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202304.0931.v2
-/

namespace Collatz.Papers.Journal_10_20944_preprints202304_0931_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jishe Feng, \"Proof the Collatz Conjecture in Binary Strings\", Preprints.org, DOI:10.20944/preprints202304.0931.v2 [2023]."

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

end Collatz.Papers.Journal_10_20944_preprints202304_0931_v2
