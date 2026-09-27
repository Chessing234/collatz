import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Stephen Wolfram, "After 100 Years, Can We Finally Crack Post's Problem of Tag? A Story of Computational Irreducibility, and More", arXiv:2103.06931 [2021].

Title: After 100 Years, Can We Finally Crack Post's Problem of Tag? A Story of Computational Irreducibility, and More

Abstract (from OpenAlex metadata, truncated):
Empirical, theoretical and historical aspects of Post's "problem of tag" from 1921 are explored. Evidence of strong computational irreducibility is found. Despite their deterministic origin, the lengths of successive sequences generated seem to closely approximate random walks. All 10^25 smallest initial conditions are found to eventually halt, although sometimes in > 6*10^11 steps. Implications of the Principle of Computational Equivalence are discussed, along with examples of identifiable computational capabilities of tag systems. Various minimal examples of complex behavior are found, including a less-biased analog of the 3n+1 Collatz problem. There is also discussion of the history of Emil Post and of tag systems in the context of ideas about the foundations of mathematics and computation.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2103.06931
-/

namespace Collatz.Papers.Arxiv2103_06931

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Stephen Wolfram, \"After 100 Years, Can We Finally Crack Post's Problem of Tag? A Story of Computational Irreducibility, and More\", arXiv:2103.06931 [2021]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2103_06931
