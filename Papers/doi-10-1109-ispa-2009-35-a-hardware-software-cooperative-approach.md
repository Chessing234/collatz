# doi-10-1109-ispa-2009-35-a-hardware-software-cooperative-approach

Citation: Yasuaki Ito and Koji Nakano, "A Hardware-Software Cooperative Approach for the Exhaustive Verification of the Collatz Conjecture", DOI:10.1109/ispa.2009.35 [2009].

Authors: Yasuaki Ito, Koji Nakano

DOI: [10.1109/ispa.2009.35](https://doi.org/10.1109/ispa.2009.35)

Year: 2009

Venue: (unknown)

Classification: verification

Abstract:

Consider the following operation on an arbitrary positive number: if the number is even, divide it by two, and if the number is odd, triple it and add one. The Collatz conjecture assert that, starting from any positive number n, repeated iteration of the operations eventually produces the value 1. The main contribution of this paper is to present hardware-software cooperative approach to verify the Collatz conjecture. The key idea of our approach is to sieve numbers n that produces 1 using a circuit implemented on an FPGA. The numbers that fail to be verified by overflow are reported to the host PC. The host PC verifies those numbers using unlimited bits operations by software. We have implemented 24 coprocessors on the Vertex II family FPGA XC2V3000-4. The experimental results show that...

Lean file: `Collatz/Papers/Journal_10_1109_ispa_2009_35.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-h (2026-09-15)
