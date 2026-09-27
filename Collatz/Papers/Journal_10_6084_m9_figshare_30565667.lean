import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Cain, Lukas, "Entropy-Theoretic Bounds on Collatz Cycles via 2-Adic Automata", 2025.

Title: Entropy-Theoretic Bounds on Collatz Cycles via 2-Adic Automata

Abstract (from harvested metadata, truncated):
Foundational whitepaper for the Discrete Arithmetic Dynamics (DAD) framework used in Drift Systems' TRL-6 entropy architecture. We provide a formal proof of the Collatz Conjecture as a boundary case of our cryptographic entropy engine, utilizing a 2-adic Finite State Automaton and a formally verified 'Basin Separation' logic. Verification: The algebraic core of this proof is formalized in Lean 4 and included as Appendix G.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.30565667
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_30565667

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Cain, Lukas, \"Entropy-Theoretic Bounds on Collatz Cycles via 2-Adic Automata\", figshare, DOI:10.6084/m9.figshare.30565667 [2025]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_30565667
