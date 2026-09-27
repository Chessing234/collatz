import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for E. Dyachenko, "Carry Logic and Palindromic Symmetry in the 2-Adic Collatz Dynamics", 2026.

Title: Carry Logic and Palindromic Symmetry in the 2-Adic Collatz Dynamics

Abstract (from harvested metadata, truncated):
We consider the normalized odd Collatz map $T(n)=(3n+1)/2^{v_2(3n+1)}$ as a discrete dynamical system in the ring of 2-adic integers. We show that the carry length $m(n)$ is strictly determined by the depth of the binary prefix match between $n$ and the unique 2-adic anchor $\alpha=-\frac13$. Closed macro-cycles are interpreted as phase-synchronized carry profiles, the existence of which requires strict palindromic symmetry of local 2-adic configurations (kernels). In terms of cylindrical topology, we prove that for a cycle length $N > 7$, an unresolvable algebraic conflict arises: the loss of injectivity of the right-edge projections is incompatible with the uniqueness of the global Diophantine invariant. This bounds the topological gluing defect ($c \le 4$), which, combined with the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19023952
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19023952

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "E. Dyachenko, \"Carry Logic and Palindromic Symmetry in the 2-Adic Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19023952 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19023952
