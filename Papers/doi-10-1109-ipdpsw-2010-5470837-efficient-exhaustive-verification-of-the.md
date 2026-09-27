# doi-10-1109-ipdpsw-2010-5470837-efficient-exhaustive-verification-of-the

Citation: Yasuaki Ito and Koji Nakano, "Efficient exhaustive verification of the Collatz conjecture using DSP48E blocks of Xilinx Virtex-5 FPGAs", DOI:10.1109/ipdpsw.2010.5470837 [2010].

Authors: Yasuaki Ito, Koji Nakano

DOI: [10.1109/ipdpsw.2010.5470837](https://doi.org/10.1109/ipdpsw.2010.5470837)

Year: 2010

Venue: (unknown)

Classification: verification

Abstract:

Consider the following operation on an arbitrary positive number: if the number is even, divide it by two, and if the number is odd, triple it and add one. The Collatz conjecture asserts that, starting from any positive number m, repeated iteration of the operations eventually produces the value 1. The main contribution of this paper is to present an efficient implementation of a coprocessor that performs the exhaustive search to verify the Collatz conjecture using a DSP48E Xilinx Virtex-5 blocks, each of which contains one multiplier and one adder. The experimental results show that, our coprocessor can verify 3.88 × 10864-bit numbers per second.

Lean file: `Collatz/Papers/Journal_10_1109_ipdpsw_2010_5470837.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-g (2026-09-15)
