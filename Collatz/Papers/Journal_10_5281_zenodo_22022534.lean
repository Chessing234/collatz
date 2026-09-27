import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Unverified Proof Claims Collatz Conjecture Decidable via Cayley Colour Graph — E8 Intelligence Research", 2026.

Title: Unverified Proof Claims Collatz Conjecture Decidable via Cayley Colour Graph — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz conjecture remains unproven; a claimed proof exists but is not peer-reviewed; one paper models the function as an automorphic Cayley colour graph, claiming decidability of \(an+b\) conjectures and a proof of the \(3n+1\) case. MATH: - Collatz map: \( f(n) = \begin{cases} n/2 & \text{if } n \equiv 0 \pmod{2} \\ 3n+1 & \text{if } n \equiv 1 \pmod{2} \end{cases} \) - Conjecture: \(\forall n \in \mathbb{N}^+, \exists k: f^k(n) = 1\) (the trivial cycle \(4 \to 2 \to 1 \to 4\)). - Paper (arXiv:2008.13643v8) claims: - Collatz graph is a connected automorphic Cayley colour graph. - Decidability of all \(an+b\) conjectures (generalized Collatz). - Proof that \(3n+1\) conjecture holds...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22022534
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22022534

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Unverified Proof Claims Collatz Conjecture Decidable via Cayley Colour Graph — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22022534 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22022534
