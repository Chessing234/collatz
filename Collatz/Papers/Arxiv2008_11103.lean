import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Anant Gupta, "On Cycles of Generalized Collatz Sequences", arXiv:2008.11103 [2020].

Title: On Cycles of Generalized Collatz Sequences

Abstract (from OpenAlex metadata, truncated):
We explore the cycles and convergence of Generalized Collatz Sequence, where $3n+1$ in original collatz function is replaced with $3n+k$. We present a generating function for cycles of GCS and show a particular inheritance structure of cycles across such sequences. The cycle structure is invariant across such inheritance and appears more fundamental than cycle elements. A consequence is that there can be arbitrarily large number of cycles in some sequences. GCS can also be seen as an integer space partition function and such partitions along with collatz graphs are inherited across sequences. An interesting connection between cycles of GCS and certain exponential Diophantine equations is also presented.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2008.11103
-/

namespace Collatz.Papers.Arxiv2008_11103

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Anant Gupta, \"On Cycles of Generalized Collatz Sequences\", arXiv:2008.11103 [2020]."

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


end Collatz.Papers.Arxiv2008_11103
