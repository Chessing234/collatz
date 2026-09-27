import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Shiravani, Amir Mohammad, "Collatz Contraction: A Two-Step Structural Model by Amir Mohammad Shiravani", 2025.

Title: Collatz Contraction: A Two-Step Structural Model by Amir Mohammad Shiravani

Abstract (from harvested metadata, truncated):
Contraction Model by Amir Mohammad Shiravani Collatz Cyclic Contraction: Analysis of the \frac{3}{2} + \frac{1}{2n} Net Growth Factor This short note presents a structural analysis focused on the core mechanism of contraction in the Collatz Conjecture. We focus on the obligatory two-step odd-even cycle (T_2(n) = \frac{3n+1}{2}), which combines an expansion step (3n+1) and a mandatory division step (\div 2). The analysis reveals that every odd step imposes a normalization identity (R(n)=2). The direct consequence is the generation of a Net Growth Factor defined by the formula \frac{3}{2} + \frac{1}{2n}. This factor demonstrates that the sequence growth asymptotically tends toward 1.5. Numeric...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17605/osf.io/2pfjc
-/

namespace Collatz.Papers.Journal_10_17605_osf_io_2pfjc

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Shiravani, Amir Mohammad, \"Collatz Contraction: A Two-Step Structural Model by Amir Mohammad Shiravani\", OSF Registries, DOI:10.17605/osf.io/2pfjc [2025]."

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

end Collatz.Papers.Journal_10_17605_osf_io_2pfjc
