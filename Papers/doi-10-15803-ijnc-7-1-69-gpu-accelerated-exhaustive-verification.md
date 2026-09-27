# doi-10-15803-ijnc-7-1-69-gpu-accelerated-exhaustive-verification

Citation: Takumi Honda et al., "GPU-accelerated Exhaustive Verification of the Collatz Conjecture", International Journal of Networking and Computing, DOI:10.15803/ijnc.7.1_69 [2017].

Authors: Takumi Honda, Yasuaki Ito, Koji Nakano

DOI: [10.15803/ijnc.7.1_69](https://doi.org/10.15803/ijnc.7.1_69)

Year: 2017

Venue: International Journal of Networking and Computing

Classification: verification

Abstract:

The main contribution of this paper is to present an implementation that performs the exhaustive search to verify the Collatz conjecture using a GPU. Consider the following operation on an arbitrary positive number: if the number is even, divide it by two, and if the number is odd, triple it and add one. The Collatz conjecture asserts that, starting from any positive number m, repeated iteration of the operations eventually produces the value 1. We have implemented it on NVIDIA GeForce GTX TITAN X and evaluated the performance. The experimental results show that, our GPU implementation can verify 1.31×1012 64-bit numbers per second. While the sequential CPU implementation on Intel Core i7-4790 can verify 5.25×109 64-bit numbers per second. Thus, our implementation on the GPU attains a...

Lean file: `Collatz/Papers/Journal_10_15803_ijnc_7_1_69.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-f (2026-09-15)
