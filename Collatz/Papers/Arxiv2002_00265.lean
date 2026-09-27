import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Derek Tucker, "Order in the Collatz: Fractal Symmetry Controlling Syracuse Function Trajectories", arXiv:2002.00265 [2020].

Title: Order in the Collatz: Fractal Symmetry Controlling Syracuse Function Trajectories

Abstract (from OpenAlex metadata, truncated):
Consider the function C(n) = {█(3n+1, n≡1 mod 2.@n/2, n≡0 mod 2.)┤ The 3x + 1 problem or Collatz conjecture asks if all trajectories iterating recursively contain one. This holds empirically but eludes theoretical proof. Remove even entries to obtain the Syracuse function, T(u), mapping odd numbers u , T(u) = (3u +1)/2r, where r maximal for T(u) odd. Here we show by expressing u as 4x ±1, a fractal regularity given by the amplitude of a periodic function passing through the x axis in the curves defined y=N cos⁡(πx/2^N ) ≡ N mod((x+2^(N-1))/2^N ,1), with ℕ the natural numbers. The expression describes the length of ascending segments R and with translation, r the number of divisions in T(u). Algebraic analysis reveals the Syracuse function’s image neatly partitions onto arithmetic progressions 6k ± 1, as a function of r. This confirms that all natural trajectories in the 3x + 1 problem co

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2002.00265
-/

namespace Collatz.Papers.Arxiv2002_00265

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Derek Tucker, \"Order in the Collatz: Fractal Symmetry Controlling Syracuse Function Trajectories\", arXiv:2002.00265 [2020]."

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

end Collatz.Papers.Arxiv2002_00265
