# doi-10-5281-zenodo-18976342-negative-feedback-the-collatz-conjecture

Citation: Clifford Keeble, "Negative Feedback: The Collatz Conjecture as a Discrete Control System", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18976342 [2026].

Authors: Clifford Keeble

DOI: [10.5281/zenodo.18976342](https://doi.org/10.5281/zenodo.18976342)

Year: 2026

Venue: Zenodo (CERN European Organization for Nuclear Research)

Classification: cycle

Abstract:

The Collatz conjecture is reframed as a discrete feedback control problem. The plant is the set of odd positive integers; the controller is the Syracuse map T(n) = (3n + 1)/2^k; the reference signal is the constant 1; and the feedback element is the +1 operation. The sign of this feedback — positive or negative — is shown to determine convergence completely. Negative feedback (3n + 1) routes every expansion class (S3) unconditionally into contraction classes (S5, S1), constituting a one-step error correction at every Syracuse iteration. Positive feedback (3n − 1) routes contraction classes back into expansion, producing the known cycles of that system. The Lyapunov function V = n/2^(Σk), proved strictly decreasing at every step, provides the formal stability certificate: no non-trivial...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_18976342.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-h (2026-09-15)
