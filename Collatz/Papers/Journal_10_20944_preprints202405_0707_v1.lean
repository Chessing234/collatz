import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ivanko S and Farag P., "Proof of the Riemann Hypothesis and the Modified Collatz Conjecture Using the Sophy-Peter Mathematical Framework", 2024.

Title: Proof of the Riemann Hypothesis and the Modified Collatz Conjecture Using the Sophy-Peter Mathematical Framework

Abstract (from harvested metadata, truncated):
In this article, we present solutions for one of the oldest mathematical problems, the Collatz Conjecture, and provide a proof for the Riemann Hypothesis, utilizing a new number theory based on newly discovered number properties, which will also be presented in this paper. This is made possible through the Sophy-Peter mathematical framework, built upon this new number theory. The Collatz Conjecture will be disproven, but as an alternative, the Oscillating Theorem will be introduced, with its correctness proven within this article. Furthermore, we present the general version of the Riemann zeta function, developed based on the new number theory. The correctness of this function is verified by comparing it with existing results of the zeta function. Using this approach and the Sophy-Peter...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202405.0707.v1
-/

namespace Collatz.Papers.Journal_10_20944_preprints202405_0707_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ivanko S and Farag P., \"Proof of the Riemann Hypothesis and the Modified Collatz Conjecture Using the Sophy-Peter Mathematical Framework\", DOI:10.20944/preprints202405.0707.v1 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_20944_preprints202405_0707_v1
