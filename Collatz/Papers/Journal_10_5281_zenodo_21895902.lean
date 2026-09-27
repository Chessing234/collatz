import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for changzheng zhou and ziqing zhou, "Collatz Constraint Network H: 2-adic Scalpel for the Collatz Map—Topological Invariant Locking of the Nonlinear Multiplicative-Additive Structure", 2026.

Title: Collatz Constraint Network H: 2-adic Scalpel for the Collatz Map—Topological Invariant Locking of the Nonlinear Multiplicative-Additive Structure

Abstract (from harvested metadata, truncated):
This paper establishes a framework of arithmetic scalpel on the ring of 2-adicintegers Z2, dissecting the nonlinear coupling of "multiply by three and add one"in the odd step of the Collatz map into a deterministic spherical map aroundthe fixed point α = −1/3. By strictly distinguishing the scope of applicationbetween the embedding of positive integers and the 2-adic extension, and usingthe positivity lemma and the descent principle as bridges, we ensure the legitimateapplication of geometric constraints within the domain of positive integers. Thecore results include: proving that the Collatz map maps the 2-adic sphere centred atα surjectively onto the sphere centred at 0, and locking the or...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21895902
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21895902

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "changzheng zhou and ziqing zhou, \"Collatz Constraint Network H: 2-adic Scalpel for the Collatz Map—Topological Invariant Locking of the Nonlinear Multiplicative-Additive Structure\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21895902 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21895902
