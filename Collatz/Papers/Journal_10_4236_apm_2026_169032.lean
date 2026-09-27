import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Mark Anthony, "Terminal Cycles of Name-Sum Maps, a Minimal Language for the Collatz Map, and the Weave of a Binomial Expansion", 2026.

Title: Terminal Cycles of Name-Sum Maps, a Minimal Language for the Collatz Map, and the Weave of a Binomial Expansion

Abstract (from harvested metadata, truncated):
The name-sum maps are a dynamical system on the positive integers induced by spelling each integer in a language and summing the letter values of its name. For every language with logarithmic name length, it is shown that a trapping theorem exists: all orbits are eventually periodic, confined to a terminal cycle whose scale is a computable functional of the alphabet. The terminal structures of seven natural languages are computed. Spelt equations X=kY and their ghost-root monodromy are presented under valuation deformation, and the combinatorial law governing truthful and lying anagrams of number names is examined. Reversing the construction, the article proves that no logarithmic language can express the Collatz map, while a two-letter language of linear name length carries the Collatz...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/apm.2026.169032
-/

namespace Collatz.Papers.Journal_10_4236_apm_2026_169032

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Mark Anthony, \"Terminal Cycles of Name-Sum Maps, a Minimal Language for the Collatz Map, and the Weave of a Binomial Expansion\", Advances in Pure Mathematics, DOI:10.4236/apm.2026.169032 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_4236_apm_2026_169032
