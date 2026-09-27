import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jonathan S. Gilbert, "A Collatz-Equivalent Map on the Nonzero Integers", arXiv:2607.0575 [2026].

Title: A Collatz-Equivalent Map on the Nonzero Integers

Abstract (from OpenAlex metadata, truncated):
The graph of the accelerated Collatz map \( T \) carries structure that is irrelevant to the Collatz conjecture: one third of its vertices are multiples of three, which no orbit can revisit, and the negative integers cannot be used at all because \( T \) admits non-trivial cycles on them. We construct an explicit conjugacy \( J \) between the conjecture-relevant vertices \( {[}{1}{]}_{3}\cup{[}{2}{]}_{3} \) and the nonzero integers \( \mathbb{Z}{*} \), yielding a map \( {K}{\colon}\ \mathbb{Z}{*}\to \mathbb{Z}{*} \) whose graph is isomorphic to the pruned Collatz graph. The Collatz conjecture becomes the statement that every \( K \)-orbit reaches the two-cycle \( \{1,-1\} \); in these coordinates the sign of an iterate records its residue class modulo \( 3 \), so every nonzero integer indexes a conjecture-relevant vertex and no non-trivial cycles are introduced. We analyze the edge struc

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2607.0575
-/

namespace Collatz.Papers.Arxiv2607_0575

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jonathan S. Gilbert, \"A Collatz-Equivalent Map on the Nonzero Integers\", arXiv:2607.0575 [2026]."

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


end Collatz.Papers.Arxiv2607_0575
