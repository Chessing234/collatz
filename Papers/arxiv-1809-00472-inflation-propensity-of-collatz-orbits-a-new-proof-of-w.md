# arxiv-1809-00472-inflation-propensity-of-collatz-orbits-a-new-proof-of-w

Citation: Fabian Bocart, "Inflation Propensity of Collatz Orbits: A New Proof-of-Work for Blockchain Applications", arXiv:1809.00472 [2018].

Authors: Fabian Bocart

arXiv: [1809.00472](https://arxiv.org/abs/1809.00472)

Year: 2018

Classification: verification

Abstract:

Cryptocurrencies like Bitcoin rely on a proof-of-work system to validate transactions and prevent attacks or double-spending. A new proof-of-work is introduced which seems to be the first number theoretic proof-of-work unrelated to primes: it is based on a new metric associated to the Collatz algorithm whose natural generalization is algorithmically undecidable: the inflation propensity is defined as the cardinality of new maxima in a developing Collatz orbit. It is numerically verified that the distribution of inflation propensity slowly converges to a geometric distribution of parameter $0.714 \approx \frac{(\pi - 1)}{3}$ as the sample size increases. This pseudo-randomness opens the door to a new class of proofs-of-work based on congruential graphs.

Lean file: `Collatz/Papers/Arxiv1809_00472.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
