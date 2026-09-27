import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Monks, Kenneth G., "On $q$-Analogs of the $3x+1$ Dynamical System", arXiv:2508.10153 [2025].

Title: On $q$-Analogs of the $3x+1$ Dynamical System

Abstract (from arXiv metadata, truncated):
The $3x+1$ Conjecture asserts that the $T$-orbit of every positive integer $x$ contains $1$, where $T$ maps $x$ to $x/2$ for $x$ even and to $(3x+1)/2$ for $x$ odd. Several authors have studied the analogous map, $T_q$, which maps $x\in F_2[q]$ to $x/q$ if $q$ divides $x$ and $((1+q)x+1)/q$ otherwise. In particular, they showed that the $T_q$-orbit of every polynomial contains $1$. This seems analogous to the $3x+1$ conjecture, but does not prove the conjecture itself, as the dynamical systems involved are not conjugate via any correspondence between polynomials and positive integers.
  In this paper, we show that $T_q$ actually is conjugate to $T$ if we extend their domains to the ring of formal power series $F_2[[q]]$ and the 2-adic integers $\mathbb{Z}_2$, respectively. Thus, it is not polynomials that correspond to positive integers via conjugacy, but rather certain formal power seri

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2508.10153
-/

namespace Collatz.Papers.Arxiv2508_10153

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Monks, Kenneth G., \"On $q$-Analogs of the $3x+1$ Dynamical System\", arXiv:2508.10153 [2025]."

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

end Collatz.Papers.Arxiv2508_10153
