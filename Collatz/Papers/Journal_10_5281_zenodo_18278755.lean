import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Miguel Cerdá Bennassar, "2-adic Scenarios in Collatz Dynamics: Preliminaries on Geometry and Odd-Step Jump Heights", 2026.

Title: 2-adic Scenarios in Collatz Dynamics: Preliminaries on Geometry and Odd-Step Jump Heights

Abstract (from harvested metadata, truncated):
This work proposes a novel geometric reading of the classical Collatz problem by rigorously separating the underlying arithmetic space from the iterated dynamics that acts upon it. Instead of starting from the iteration of the Collatz function, we first introduce a fixed, pre‑dynamic geometric organization of the natural numbers: the 2-adic table‑scenario, based on the unique decomposition of every integer as an odd part times a power of two. This scenario provides a global coordinate system that is independent of any particular trajectory. A second, complementary scenario is then defined on the set of odd numbers alone. It classifies each odd integer according to the 2-adic height of its successor under the Collatz map—that is, according to how many consecutive divisions by two are...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18278755
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18278755

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Miguel Cerdá Bennassar, \"2-adic Scenarios in Collatz Dynamics: Preliminaries on Geometry and Odd-Step Jump Heights\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18278755 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18278755
