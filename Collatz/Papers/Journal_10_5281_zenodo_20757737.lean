import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sugianto, Ogin, "A Structural Framework for the Collatz Conjecture: Affine Partitions, 2-Adic Accumulation, Boundary Conditions, Cycle Equations, and the Global Surplus Gap", 2026.

Title: A Structural Framework for the Collatz Conjecture: Affine Partitions, 2-Adic Accumulation, Boundary Conditions, Cycle Equations, and the Global Surplus Gap

Abstract (from harvested metadata, truncated):
We present a comprehensive structural framework for the Collatz conjecture, built upon the Collatzogin Tree. The tree partitions all positive integers via affine maps of the form:\[T_{t,k,c}(n) = \frac{3^t n + c}{2^k},\]where \(t\) is the number of odd steps, \(k\) the number of halving steps, and \(c \in \mathbb{Z}_{\ge 0}\) an affine constant. We rigorously prove several foundational results: The affine composition laws and tree structure. The depth function \(D := k - t\log_2(3)\) and Terras' criterion (\(D > 0 \implies\) descent). The complete residue dynamics modulo \(4\). 2-adic Accumulation Lemma: persistent residence in \(3 \pmod{4}\) is finite and bounded by \(\lfloor \log_2(a+1) \r...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20757737
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20757737

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sugianto, Ogin, \"A Structural Framework for the Collatz Conjecture: Affine Partitions, 2-Adic Accumulation, Boundary Conditions, Cycle Equations, and the Global Surplus Gap\", Zenodo, DOI:10.5281/zenodo.20757737 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20757737
