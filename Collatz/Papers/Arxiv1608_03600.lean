import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sawon Pratiher, "Recurrence Structures, Finite State Decomposition, and Statistical Bias in Collatz Path Sequences", arXiv:1608.03600 [2016].

Title: Recurrence Structures, Finite State Decomposition, and Statistical Bias in Collatz Path Sequences

Abstract (from OpenAlex metadata, truncated):
We investigate the structure of Collatz path sequences $\{F^k(n)\}_{k=0}^{\infty}$ for positive integers $n$, where $F$ denotes the standard Collatz map. By classifying natural numbers into residue classes modulo~4, we establish that the Collatz conjecture reduces to verifying convergence for integers congruent to $3 \pmod{4}$. For this class, we identify six recurrent forms -- residue classes modulo~9 -- through which the path sequence elements cycle, and we prove that these forms are \emph{complete} in the sense that every power of~2 belongs to exactly one of them. We construct a deterministic finite state machine (FSM) whose states correspond to these six forms and whose transitions encode the Collatz dynamics, yielding a system of coupled functional equations involving linear congruences. We prove closed-form characterizations of the power-of-2 elements within three of the six recurr

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1608.03600
-/

namespace Collatz.Papers.Arxiv1608_03600

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sawon Pratiher, \"Recurrence Structures, Finite State Decomposition, and Statistical Bias in Collatz Path Sequences\", arXiv:1608.03600 [2016]."

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


end Collatz.Papers.Arxiv1608_03600
