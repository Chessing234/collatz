import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduardo Santana, "Thermodynamic Dictionary for Syracuse-like Maps", arXiv:2601.03297 [2026].

Title: Thermodynamic Dictionary for Syracuse-like Maps

Abstract (from OpenAlex metadata, truncated):
In this paper we estabilsh a dictionary between the behavior of a general map $f: X \to X$ which is defined by using a decomposition into disjoint subsets $X = A \cup B$ and the thermodynamic formalism. The approach of this paper is set theoretical, topological and ergodic. We define a key topology and consider its Borel $σ$-algebra in order to study the thermodynamic formalism for the general setting, proving that recurrence implies periodicity, the topological entropy is zero, we can decompose the invariant measures into a general sum of ergodic ones and we establish a dictionary between the cycles and the equilibrium states of continuous potentials. All this is done for the general setting, with applications for the Syracuse maps and the Collatz map in particular, as a significant application of the dictionary, proving the finiteness of cycles.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2601.03297
-/

namespace Collatz.Papers.Arxiv2601_03297

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduardo Santana, \"Thermodynamic Dictionary for Syracuse-like Maps\", arXiv:2601.03297 [2026]."

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


end Collatz.Papers.Arxiv2601_03297
