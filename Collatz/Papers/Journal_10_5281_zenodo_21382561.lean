import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for LI, Jian, "A Proof of the Collatz Conjecture via Mod‑4 Classification and Emission‑Braking Counting", 2026.

Title: A Proof of the Collatz Conjecture via Mod‑4 Classification and Emission‑Braking Counting

Abstract (from harvested metadata, truncated):
This paper proves the Collatz conjecture using mod‑4 classification and an emission‑braking counting framework. Even numbers of the form 2a reduce directly to 1; for general even numbers 2a×m(with m>1 odd), after a successive divisions by 2 they reduce to the odd number m. Hence it suffices to prove that every odd number converges to 1. By introducing "emission" and "braking" to describe the odd and even transformations respectively, we represent the odd iteration as the atomic operation . Positive odd integers are classified modulo 4 into type‑3 (3mod 4) and type‑1(1mod 4), and we analyze the surplus/deficit difference between the two types. It is proved that every "consecutive" type‑3 segm...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21382561
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21382561

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "LI, Jian, \"A Proof of the Collatz Conjecture via Mod‑4 Classification and Emission‑Braking Counting\", Zenodo, DOI:10.5281/zenodo.21382561 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21382561
