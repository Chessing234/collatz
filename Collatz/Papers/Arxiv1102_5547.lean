import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jonathan Yazinski, "Pseudoperiodicity and the $3x+1$ Conjugacy Function", arXiv:1102.5547 [2011].

Title: Pseudoperiodicity and the $3x+1$ Conjugacy Function

Abstract (from OpenAlex metadata, truncated):
The 3x+1 function T is defined on the positive integers by $T(x) = \frac{3x+1}{2}$ for x odd and $T(x) = \frac{x}{2}$ for x even. The function T has a natural extension to the 2-adic integers, and there is a continuous function $Φ$ which conjugates T to the 2-adic shift map $σ$. Bernstein and Lagarias conjectured that -1 and 1/3 are the only odd fixed points of $Φ$. In this paper we investigate periodicity associated with $Φ$, a property of the map which is a natural extention of solenoidality. We use it to show that there are nontrivial infinite families of 2-adics that are not fixed points of $Φ$. In particular, we prove that three sequences of farPoints of 2-adic integers are finitely pseudoperiodic, providing more evidence supporting the $Φ$ Fixed Point Conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1102.5547
-/

namespace Collatz.Papers.Arxiv1102_5547

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jonathan Yazinski, \"Pseudoperiodicity and the $3x+1$ Conjugacy Function\", arXiv:1102.5547 [2011]."

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

end Collatz.Papers.Arxiv1102_5547
