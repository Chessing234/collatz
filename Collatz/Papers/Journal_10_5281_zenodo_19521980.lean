import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ueoka, Yoshiki, "A Proof of the Negative Collatz Conjecture via Alternating Binary Notation and Collatz Phase Expressions", 2026.

Title: A Proof of the Negative Collatz Conjecture via Alternating Binary Notation and Collatz Phase Expressions

Abstract (from harvested metadata, truncated):
In this paper, we treat the negative Collatz conjecture not as a problem of tracing negative integers point by point, but as a structural problem obtained by reducing it, via absolute values, to the accelerated odd map $$F_-(n)=\frac{3n-1}{2^{\nu_2(3n-1)}} \qquad (n\ \text{odd},\ n>0),$$ and then describing this map in terms of alternating binary notation (ABN) and Collatz phase expressions (CPE). The translation machinery, the local 27-pattern analysis, the carry-reach bound $$\le 2$$, the one-step inequalities for the structural quantities $$(\mu,H_{CS},H_K,B),$$ and the finite descent in the high-mu region are inherited from the positive Collatz side through the $$p\leftrightarrow m$$ sym...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19521980
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19521980

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ueoka, Yoshiki, \"A Proof of the Negative Collatz Conjecture via Alternating Binary Notation and Collatz Phase Expressions\", Zenodo, DOI:10.5281/zenodo.19521980 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19521980
