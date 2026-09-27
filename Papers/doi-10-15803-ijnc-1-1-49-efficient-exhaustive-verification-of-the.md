# doi-10-15803-ijnc-1-1-49-efficient-exhaustive-verification-of-the

Citation: Yasuaki Ito and Koji Nakano, "Efficient Exhaustive Verification of the Collatz Conjecture using DSP blocks of Xilinx FPGAs", International Journal of Networking and Computing, DOI:10.15803/ijnc.1.1_49 [2011].

Authors: Yasuaki Ito, Koji Nakano

DOI: [10.15803/ijnc.1.1_49](https://doi.org/10.15803/ijnc.1.1_49)

Year: 2011

Venue: International Journal of Networking and Computing

Classification: verification

Abstract:

Consider the following operation on an arbitrary positive number: if the number is even, divide it by two, and if the number is odd, triple it and add one. The Collatz conjecture asserts that, starting from any positive number m, repeated iteration of the operations eventually produces the value 1. The main contribution of this paper is to present an efficient implementation of a coprocessor that performs the exhaustive search to verify the Collatz conjecture using a Xilinx Virtex-6 FPGA with DSP blocks, each of which contains one multiplier and one adder. The experimental results show that, our coprocessor can verify 4.99 × 108 64-bit numbers per second. Also, we have implemented a multi-coprocessors system that has 380 coprocessors on the FPGA. The experimental results show that our...

Lean file: `Collatz/Papers/Journal_10_15803_ijnc_1_1_49.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-f (2026-09-15)
