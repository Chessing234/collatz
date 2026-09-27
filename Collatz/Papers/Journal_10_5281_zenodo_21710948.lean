import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for William Betancourt Reyes, "A Modular Structure for the Collatz Dynamics: Upper Bound and Uniqueness of the 4–2–1 Cycle", 2026.

Title: A Modular Structure for the Collatz Dynamics: Upper Bound and Uniqueness of the 4–2–1 Cycle

Abstract (from harvested metadata, truncated):
This work introduces a modular mechanism for controlling Collatz orbits through two operators: the projection function S(n) and the elevator E(n)=n·64^k. The function S(n) is defined through a complete classification of residues modulo 18 and maps every natural number directly into the stable class 16 (mod 36). This projection is fully compatible with the closed modular structure of the even Collatz dynamics, where all even values eventually fall inside the system {4, 16, 22, 34} (mod 36). Within this structure, the classes 22 and 34 act as corridors leading to 16, while the classes 10 and 28 disappear after the first cycle. Although S(n) always lands in the contractive class 16, its value may lie below the true peak of the orbit. To resolve this, the elevator operator E(n)=n·64^k is...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21710948
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21710948

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "William Betancourt Reyes, \"A Modular Structure for the Collatz Dynamics: Upper Bound and Uniqueness of the 4–2–1 Cycle\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21710948 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21710948
