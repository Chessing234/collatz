import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Diedrich, "Bidirectional Dynamics in the Collatz Problem: A Complete Resolution", arXiv:2505.01372 [2025].

Title: Bidirectional Dynamics in the Collatz Problem: A Complete Resolution

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture states that iterating the function $C(n) = n/2$ for even $n$ and $C(n) = 3n+1$ for odd $n$ eventually leads to 1 for any positive integer $n$. Despite its elementary formulation, the conjecture has resisted resolution for over 80 years. This paper introduces a novel bidirectional approach that analyzes both forward trajectories and backward paths simultaneously. We establish two independent properties: (1) all backward paths under the generator function (a multivalued mapping that inverts the Collatz function) are finite and terminate at elements of $\{1,2,4\}$, and (2) $\{1,4,2\}$ is the unique cycle in the Collatz system. We then construct a formal structural bridge connecting these properties, proving that all Collatz sequences must reach 1. Our work introduces a global convergence measure that rigorously prohibits divergent orbits and provides explicit bounds o

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2505.01372
-/

namespace Collatz.Papers.Arxiv2505_01372

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Diedrich, \"Bidirectional Dynamics in the Collatz Problem: A Complete Resolution\", arXiv:2505.01372 [2025]."

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

end Collatz.Papers.Arxiv2505_01372
