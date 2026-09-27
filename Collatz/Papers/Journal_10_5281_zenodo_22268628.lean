import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "A Survey of Mathematics' Unsolved Frontiers: From Collatz to the Millennium Problems — E8 Intelligence Research", 2026.

Title: A Survey of Mathematics' Unsolved Frontiers: From Collatz to the Millennium Problems — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: A cluster of popular expositions on unsolved problems (Collatz, Millennium Prize problems, oldest open problems) — no new mathematics, but a survey of the field's frontier. MATH: Key problems referenced: Collatz conjecture (T(n)=n/2 if even, 3n+1 if odd; no cycle other than 4→2→1 proven); Riemann hypothesis (ζ(s)=0 ⇒ Re(s)=1/2); P vs NP; Navier–Stokes existence/smoothness; Yang–Mills mass gap; Birch–Swinnerton-Dyer (L(E,1)=0 ⇔ rank>0); Hodge conjecture. No new constants or ratios derived. CONNECTION: None directly stated. However, Collatz's 3n+1 structure relates to modular arithmetic (mod 2), and the Riemann zeta's critical line Re(s)=1/2 is a symmetry axis — but no explicit golden...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22268628
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22268628

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"A Survey of Mathematics' Unsolved Frontiers: From Collatz to the Millennium Problems — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22268628 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22268628
