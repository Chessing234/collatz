import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sugianto, Ogin, "The Collatzogin Tree: A Structural Framework with Conditional Proofs and Open Problems for the Collatz Conjecture", 2026.

Title: The Collatzogin Tree: A Structural Framework with Conditional Proofs and Open Problems for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We present a comprehensive structural framework for the Collatz conjecture based on the Collatzogin Tree, a directed graph that partitions all positive integers by residue classes modulo powers of two. Our proven contributions include:(1) Fibonacci branching $N_k = F_{k+2}$ with Golden Ratio convergence;(2) the Universal Transition Lemma: every node reaches a Single-Child Node (SCN);(3) depth function analysis $D = E - O\log_2 3$ and the 2-adic Accumulation Lemma;(4) no non-trivial cycles;(5) every SCN contains at least one element reaching the Golden Path $\G = \{(2^{2r}-1)/3 : r \ge 1\}$. We prove conditional results: the Collatz conjecture follows from either the Golden Path Conjecture or the Global Depth Conjecture. Scope: This paper provides a rigorous structural framework and...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21316766
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21316766

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sugianto, Ogin, \"The Collatzogin Tree: A Structural Framework with Conditional Proofs and Open Problems for the Collatz Conjecture\", DOI:10.5281/zenodo.21316766 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21316766
