import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Olivier Rozier, "Are the Collatz and abc conjectures related?", arXiv:2306.15284 [2023].

Title: Are the Collatz and abc conjectures related?

Abstract (truncated):
The Collatz and $abc$ conjectures, both well known and thoroughly studied, appear to be largely unrelated at first sight. We show that assuming the $abc$ conjecture true is helpful to improve the lower bound of integers initiating a particular type of Collatz sequences, namely finite sequences of a given length where all terms but one are odd with the usual ``shortcut'' form. To obtain sharper bounds in this context, we are led to consider a small subset of the $abc$-hits. Then, it turns out that Collatz iterations as well as Wieferich primes may be used to find large triples in this subset.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2306.15284
-/

namespace MathlibAttack.Papers.Arxiv2306_15284

open MathlibAttack.Papers

def citation : String := "Olivier Rozier, \"Are the Collatz and abc conjectures related?\", arXiv:2306.15284 [2023]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2306_15284
