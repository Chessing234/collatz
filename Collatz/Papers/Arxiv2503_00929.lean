import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Amarachukwu Nwankpa, "The Collatz Conjecture: A Graph-Theoretic Structural Proof", arXiv:2503.00929 [2025].

Title: The Collatz Conjecture: A Graph-Theoretic Structural Proof

Abstract (from OpenAlex metadata, truncated):
This paper presents a structural proof of the Collatz Conjecture by demonstrating that the Collatz map operates within a finite structural framework. We formalize this framework as a \textbf{17-state Finite State Machine (FSM)} derived directly from the modular properties and integer partitions intrinsic to the Collatz function. The core of the proof lies in a rigorous graph-theoretic analysis of this FSM. We prove that all states representing integers not in the terminal cycle $\{1, 2, 4\}$ form a single \emph{Strongly Connected Component} (SCC), and that this SCC possesses a \emph{unique exit transition} leading irreversibly to the states corresponding to the terminal cycle. By the fundamental properties of finite directed graphs, these structural invariants guarantee that any trajectory---represented as a path through the FSM---must reach the unique terminal cycle in finitely many ste

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2503.00929
-/

namespace Collatz.Papers.Arxiv2503_00929

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Amarachukwu Nwankpa, \"The Collatz Conjecture: A Graph-Theoretic Structural Proof\", arXiv:2503.00929 [2025]."

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

end Collatz.Papers.Arxiv2503_00929
