import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Erhan Tezcan, "On Collatz Conjecture", arXiv:1902.07312 [2019].

Title: On Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz Conjecture can be stated as: using the reduced Collatz function $C(n) = (3n+1)/2^x$ where $2^x$ is the largest power of 2 that divides $3n+1$, any odd integer $n$ will eventually reach 1 in $j$ iterations such that $C^j(n) = 1$. In this paper we use reduced Collatz function and reverse reduced Collatz function. We present odd numbers as sum of fractions, which we call `fractional sum notation' and its generalized form `intermediate fractional sum notation', which we use to present a formula to obtain numbers with greater Collatz sequence lengths. We give a formula to obtain numbers with sequence length 2. We show that if trajectory of $n$ is looping and there is an odd number $m$ such that $C^j(m) = 1$, $n$ must be in form $3^j\times2k + 1, k \in \mathbb{N}_0$ where $C^j(n) = n$. We use Intermediate fractional sum notation to show a simpler proof that there are no loops with 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1902.07312
-/

namespace Collatz.Papers.Arxiv1902_07312

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Erhan Tezcan, \"On Collatz Conjecture\", arXiv:1902.07312 [2019]."

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


end Collatz.Papers.Arxiv1902_07312
