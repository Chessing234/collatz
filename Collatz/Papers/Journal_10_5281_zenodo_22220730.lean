import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aaron Kyle Solomon, "Polynomial Boundary Coordinates for Collatz Cycles", 2026.

Title: Polynomial Boundary Coordinates for Collatz Cycles

Abstract (from harvested metadata, truncated):
A finite parity word determines a rational periodic orbit of the shortcut Collatz map. For the classes studied here, integral realizability is encoded by a sparse polynomial boundary that vanishes at a canonical modular unit exactly when the orbit is integral. Let $n$ be the length of the parity word and u its number of odd steps. The main construction treats hypothetical positive cycles where n and u are coprime. We compare a parity word with the balanced reference pattern having the same $n$ and $u$—the upper-Christoffel word. We then establish a unique rooted rotation of this parity word. The differences between the cumulative zero counts of this rotation and the upper-Christoffel word fo...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22220730
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22220730

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aaron Kyle Solomon, \"Polynomial Boundary Coordinates for Collatz Cycles\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22220730 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22220730
