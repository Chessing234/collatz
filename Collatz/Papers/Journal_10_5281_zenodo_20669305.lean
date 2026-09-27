import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for John Janik, "Finite Spectral Shadows for the Collatz Valuation Cocycle", 2026.

Title: Finite Spectral Shadows for the Collatz Valuation Cocycle

Abstract (from harvested metadata, truncated):
We study residue equidistribution for the accelerated Collatz/Syracuse map$S(x)=(3x+1)/2^{v_2(3x+1)}$ through a pathwise twisted Birkhoff functional---the\emph{deterministic defect cocycle} $W_n(x;\chi,s)$---and the finiteresidue--height transfer operators $\Lcal_{s,Q,L,\chi}$ that govern it. Our aimis not to prove the Collatz conjecture but to identify, rigorously, the correctfinite spectral object and the correct quotient on which its gap should besought. We prove two clean finite identities: a \emph{sliding-window congruence}expressing $x_n\bmod 3^r$ as a finite window of the valuation word, and the factthat the quadratic character $\chi_2$ of $(\Z/3^r)^\times$ satisfies$\chi_2(S(x))=(-1)...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20669305
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20669305

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "John Janik, \"Finite Spectral Shadows for the Collatz Valuation Cocycle\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20669305 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20669305
