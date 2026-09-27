import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for William Betancourt Reyes, "A Modular Roof Structure for Collatz Dynamics II: A Closed Modular System for Roof Descent", 2026.

Title: A Modular Roof Structure for Collatz Dynamics II: A Closed Modular System for Roof Descent

Abstract (from harvested metadata, truncated):
This work complements and extends the results of the author's previous manuscript, where a modular structure was introduced to analyze the dynamics of the Collatz function through a modular transformation \(S(n)\) and a roof function \(T(n)\). In this continuation, we show that the dynamics of roofs are governed by a closed modular system consisting only of the classes \(4,16,22,34 \pmod{36}\). After the first cycle, odd numbers congruent to \(3 \pmod{6}\) disappear from the orbit, eliminating the classes \(10\) and \(28 \pmod{36}\). A complete classification according to \(n \pmod{6}\), \(n \pmod{9}\), and \(n \pmod{4}\) shows that stable roofs arise exclusively from odd numbers \(5 \pmod{6}\), and that all roofs satisfy \(T(n)\equiv 16\pmod{36}\). This closed modular system explains why...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20493450
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20493450

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "William Betancourt Reyes, \"A Modular Roof Structure for Collatz Dynamics II: A Closed Modular System for Roof Descent\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20493450 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20493450
