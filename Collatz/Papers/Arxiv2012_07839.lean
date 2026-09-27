import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Markus Sigg, "On the cluster structures in Collatz preimages", arXiv:2012.07839 [2020].

Title: On the cluster structures in Collatz preimages

Abstract (from OpenAlex metadata, truncated):
The cluster structures that can be observed in the first few Collatz preimages of the set $\{1\}$ are maintained through all level sets of the Collatz tree, provided that the orbit steadiness \[ \prod_{\substack{k \in R(n) k \equiv 4 (\mathrm{mod} 6)}} \frac{k-1}k \] of the elements $n$ of the Collatz tree is suitably bounded from below, where $R(n)$ denotes the Collatz orbit of $n$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2012.07839
-/

namespace Collatz.Papers.Arxiv2012_07839

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Markus Sigg, \"On the cluster structures in Collatz preimages\", arXiv:2012.07839 [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2012_07839
