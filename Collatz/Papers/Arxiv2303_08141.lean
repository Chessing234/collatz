import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for M. Bruschi and F. Calogero, "Variations on a Theme of Collatz", arXiv:2303.08141 [2023].

Title: Variations on a Theme of Collatz

Abstract (from OpenAlex metadata, truncated):
Consider the recursive relation generating a new positive integer $n_{\ell +1}$ from the positive integer $n_{\ell }$ according to the following simple rules: if the integer $n_{\ell }$ is odd, $n_{\ell +1}=3n_{\ell }+1$; if the integer $n_{\ell }$ is even, $n_{\ell +1}=n_{\ell }/2$. The so-called Collatz conjecture states that, starting from any positive integer $N$, the recursion characterized by the continued application of these rules ends up in the cycle $4,$ $2,1$. This conjecture is generally believed to be true (on the basis of extensive numerical checks), but it is as yet unproven. In this paper -- based on the assumption that the Collatz conjecture is indeed true -- we present a quite simple extension of it, which entails the possibility to divide all natural numbers into $3$ disjoint classes, to each of which we conjecture -- on the basis of (not very extensive) numerical checks -- $1/3$ of all natural numbers belong; or, somewhat equivalently, to $2$ disjoint classes, to wh

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2303.08141
-/

namespace Collatz.Papers.Arxiv2303_08141

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "M. Bruschi and F. Calogero, \"Variations on a Theme of Collatz\", arXiv:2303.08141 [2023]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2303_08141
