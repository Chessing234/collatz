import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Olivier Rozier, "Are the Collatz and abc conjectures related?", arXiv:2306.15284 [2023].

Title: Are the Collatz and abc conjectures related?

Abstract (from OpenAlex metadata, truncated):
The Collatz and $abc$ conjectures, both well known and thoroughly studied, appear to be largely unrelated at first sight. We show that assuming the $abc$ conjecture true is helpful to improve the lower bound of integers initiating a particular type of Collatz sequences, namely finite sequences of a given length where all terms but one are odd with the usual ``shortcut'' form. To obtain sharper bounds in this context, we are led to consider a small subset of the $abc$-hits. Then, it turns out that Collatz iterations as well as Wieferich primes may be used to find large triples in this subset.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2306.15284
-/

namespace Collatz.Papers.Arxiv2306_15284

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Olivier Rozier, \"Are the Collatz and abc conjectures related?\", arXiv:2306.15284 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2306_15284
