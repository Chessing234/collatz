import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture Unproven: Key Source Is Unvalidated arXiv Preprint — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Unproven: Key Source Is Unvalidated arXiv Preprint — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz conjecture remains unproven; most cited sources are popular expositions or claimed proofs without peer-reviewed validation. The only substantive mathematical work is an arXiv preprint (2008.13643v8) framing Collatz as an automorphic Cayley colour graph, claiming decidability of generalized $an+b$ conjectures and a proof of $3n+1$. | MATH: Collatz map: $T(n) = n/2$ if $n$ even, $T(n) = 3n+1$ if $n$ odd. Conjecture: $\forall n \in \mathbb{N}, \exists k: T^k(n) = 1$. The preprint's core structure: Collatz graph as a Cayley graph with automorphism group acting on colour classes; root cycle $4 \to 2 \to 1 \to 4$; branching number $c=4$. No explicit new constants or ratios extract...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22630171
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22630171

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture Unproven: Key Source Is Unvalidated arXiv Preprint — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22630171 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22630171
