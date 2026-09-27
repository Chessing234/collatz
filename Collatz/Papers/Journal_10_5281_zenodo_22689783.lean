import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Residue-Class Reduction of Collatz to 1 mod 4 Cases — E8 Intelligence Research", 2026.

Title: Residue-Class Reduction of Collatz to 1 mod 4 Cases — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The Collatz recurrence, when analyzed via residue classes modulo 4, reduces the conjecture to checking convergence only for integers congruent to 1 mod 4 — a structural simplification that parallels lattice/root-system reduction. The Borel sigma-algebra videos are pedagogical, not novel; the arXiv paper is the substantive finding. MATH: - Collatz map: \( F(n) = n/2 \) if \( n \) even; \( F(n) = (3n+1)/2 \) if \( n \) odd. - Residue classes mod 4: \( n \equiv 0,1,2,3 \pmod{4} \). - Key reduction: If \( n \equiv 3 \pmod{4} \), then \( F(n) \equiv 1 \pmod{4} \) after one step (since \( 3(4k+3)+1 = 12k+10 = 2(6k+5) \), and \( 6k+5 \equiv 1 \pmod{4} \)). - Thus the entire orbit's converg...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22689783
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22689783

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Residue-Class Reduction of Collatz to 1 mod 4 Cases — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22689783 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22689783
