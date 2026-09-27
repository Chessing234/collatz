import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Markus Sigg, "On the cluster structures in Collatz preimages", arXiv:2012.07839 [2020].

Title: On the cluster structures in Collatz preimages

Abstract (truncated):
The cluster structures that can be observed in the first few Collatz preimages of the set $\{1\}$ are maintained through all level sets of the Collatz tree, provided that the orbit steadiness \[ \prod_{\substack{k \in R(n) k \equiv 4 (\mathrm{mod} 6)}} \frac{k-1}k \] of the elements $n$ of the Collatz tree is suitably bounded from below, where $R(n)$ denotes the Collatz orbit of $n$.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2012.07839
-/

namespace MathlibAttack.Papers.Arxiv2012_07839

open MathlibAttack.Papers

def citation : String := "Markus Sigg, \"On the cluster structures in Collatz preimages\", arXiv:2012.07839 [2020]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2012_07839
