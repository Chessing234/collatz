import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jeffrey R. Goodwin, "The 3x+1 Problem and Integer Representations", arXiv:1504.03040 [2015].

Title: The 3x+1 Problem and Integer Representations

Abstract (from OpenAlex metadata, truncated):
The $3x+1$ Problem asks if whether for every natural number $n$, there exists a finite number of iterations of the piecewise function $$f(2n)=n, \quad f(2n-1)=6n-2, $$ with an iterate equal to the number $1$, or in other words, every sequence contains the trivial cycle $\left\langle {4,2,1}\right\rangle$. We use a set-theoretic approach to get representations of all inverse iterates of the number $1$. The representations, which are exponential Diophantine equations, help us study both the \textit{mixing} property of $f$ and the asymptotic behavior of sequences containing the trivial cycle. Another one of our original results is the new insight that the \textit{ones-ratio} approaches zero for such sequences, where the number of odd terms is \textit{arbitrarily large}.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1504.03040
-/

namespace Collatz.Papers.Arxiv1504_03040

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jeffrey R. Goodwin, \"The 3x+1 Problem and Integer Representations\", arXiv:1504.03040 [2015]."

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


end Collatz.Papers.Arxiv1504_03040
