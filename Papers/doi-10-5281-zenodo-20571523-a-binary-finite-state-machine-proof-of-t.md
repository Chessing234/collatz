# doi-10-5281-zenodo-20571523-a-binary-finite-state-machine-proof-of-t

Citation: 王, 江祁, "A Binary Finite State Machine Proof of the Collatz Conjecture 科拉茨猜想的二进制有限状态机证明", DOI:10.5281/zenodo.20571523 [2026].

Authors: 王, 江祁

DOI: [10.5281/zenodo.20571523](https://doi.org/10.5281/zenodo.20571523)

Year: 2026

Venue: (unknown)

Classification: verification

Abstract:

This paper presents a rigorous proof of the Collatz conjecture using a binary finite state machine approach. The core insight is that under binary representation, the Collatz operations exhibit strict locality. For odd numbers congruent to 3 modulo 4 — the only case requiring detailed analysis — the operation (3N+1)/2 is shown to have exactly one carry bit and one division by 2, yielding a net carry of zero. The carry propagation always terminates within a 6-bit window, and the state space of 64 possible 6-bit patterns is strictly closed under the operation. Within this closed state space, only 16 states (those ending in binary "11") require tracking. A set of elimination rules is introduced, and exhaustive enumeration verifies that all 16 "stubborn" states exit the stubborn set in...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20571523.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
