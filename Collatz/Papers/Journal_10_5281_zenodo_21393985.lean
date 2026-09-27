import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Keshava Prasad Halemane, "Halemane's Theorem on the Collatz (3n+1) System", 2026.

Title: Halemane's Theorem on the Collatz (3n+1) System

Abstract (from harvested metadata, truncated):
Halemane’s Theorem on the Collatz (3n+1) System © Dr.(Prof.) Keshava Prasad Halemane, Professor - retired (2017JAN31) from Department of Mathematical And Computational Sciences, National Institute of Technology Karnataka Surathkal, Srinivasnagar, Mangaluru - 575025, India. https://orcid.org/0000-0003-3483-3521 Independent Researcher @ SASHESHA (no affiliations; no funding; no data used; no conflict of interests) https://www.linkedin.com/in/keshavaprasadahalemane/ k.prasad.h@gmail.com Abstract Halemane’s Theorem on the Collatz (3n+1) System states that the entire dynamics of the Collatz (3n+1) System and therefore the entire Collatz-Map defined by the transitive closure of the Collatz Functio...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21393985
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21393985

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Keshava Prasad Halemane, \"Halemane's Theorem on the Collatz (3n+1) System\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21393985 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21393985
