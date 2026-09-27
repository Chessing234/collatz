import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lezama Esquivel, Juan Thor, "Thor's Demonstration of the Collatz Conjecture: A Formal Proof Through Modular Structure and Energy Descent.", 2025.

Title: Thor's Demonstration of the Collatz Conjecture: A Formal Proof Through Modular Structure and Energy Descent.

Abstract (from harvested metadata, truncated):
This paper presents a formal and deterministic proof of the Collatz Conjecture, structured around a modular classification of odd integers, a valuation-based energy function, and descent dynamics analogous to a Lyapunov process. By classifying behavior in modular cycles and proving the impossibility of non-trivial loops through algebraic and valuation-based arguments, the approach demonstrates convergence for all positive integers. Unlike heuristic or probabilistic attempts, this proof leverages a self-contained and elementary yet structurally deep framework.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/2zskf_v1
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_2zskf_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lezama Esquivel, Juan Thor, \"Thor's Demonstration of the Collatz Conjecture: A Formal Proof Through Modular Structure and Energy Descent.\", DOI:10.31219/osf.io/2zskf_v1 [2025]."

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

end Collatz.Papers.Journal_10_31219_osf_io_2zskf_v1
