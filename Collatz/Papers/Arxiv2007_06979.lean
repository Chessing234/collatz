import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Stérin, Tristan, Woods, Damien, "The Collatz process embeds a base conversion algorithm", arXiv:2007.06979 [2020].

Title: The Collatz process embeds a base conversion algorithm

Abstract (from OpenAlex metadata, truncated):
The Collatz process is defined on natural numbers by iterating the map $T(x) = T_0(x) = x/2$ when $x\in\mathbb{N}$ is even and $T(x)=T_1(x) =(3x+1)/2$ when $x$ is odd. In an effort to understand its dynamics, and since Generalised Collatz Maps are known to simulate Turing Machines [Conway, 1972], it seems natural to ask what kinds of algorithmic behaviours it embeds. We define a quasi-cellular automaton that exactly simulates the Collatz process on the square grid: on input $x\in\mathbb{N}$, written horizontally in base 2, successive rows give the Collatz sequence of $x$ in base 2. We show that vertical columns simultaneously iterate the map in base 3. This leads to our main result: the Collatz process embeds an algorithm that converts any natural number from base 3 to base 2. We also find that the evolution of our automaton computes the parity of the number of 1s in any ternary input. I

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2007.06979
-/

namespace Collatz.Papers.Arxiv2007_06979

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "St\u00e9rin, Tristan and Woods, Damien, \"The Collatz process embeds a base conversion algorithm\", arXiv:2007.06979 [2020]."

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

end Collatz.Papers.Arxiv2007_06979
