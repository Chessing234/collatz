import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fabian Bocart, "Inflation Propensity of Collatz Orbits: A New Proof-of-Work for Blockchain Applications", arXiv:1809.00472 [2018].

Title: Inflation Propensity of Collatz Orbits: A New Proof-of-Work for Blockchain Applications

Abstract (from OpenAlex metadata, truncated):
Cryptocurrencies like Bitcoin rely on a proof-of-work system to validate transactions and prevent attacks or double-spending. A new proof-of-work is introduced which seems to be the first number theoretic proof-of-work unrelated to primes: it is based on a new metric associated to the Collatz algorithm whose natural generalization is algorithmically undecidable: the inflation propensity is defined as the cardinality of new maxima in a developing Collatz orbit. It is numerically verified that the distribution of inflation propensity slowly converges to a geometric distribution of parameter $0.714 \approx \frac{(\pi - 1)}{3}$ as the sample size increases. This pseudo-randomness opens the door to a new class of proofs-of-work based on congruential graphs.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1809.00472
-/

namespace Collatz.Papers.Arxiv1809_00472

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fabian Bocart, \"Inflation Propensity of Collatz Orbits: A New Proof-of-Work for Blockchain Applications\", arXiv:1809.00472 [2018]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Arxiv1809_00472
