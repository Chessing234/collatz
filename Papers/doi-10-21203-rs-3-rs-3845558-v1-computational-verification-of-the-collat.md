# doi-10-21203-rs-3-rs-3845558-v1-computational-verification-of-the-collat

Citation: David Barina, "Computational Verification of the Collatz Problem", Research Square, DOI:10.21203/rs.3.rs-3845558/v1 [2024].

Authors: David Barina

DOI: [10.21203/rs.3.rs-3845558/v1](https://doi.org/10.21203/rs.3.rs-3845558/v1)

Year: 2024

Venue: Research Square

Classification: verification

Abstract:

Abstract This article presents our project, which aims to verify the convergence of the Collatz problem computationally. As a main point of the article, we introduce a new result that pushes the limit for which the problem is verified up to 1.5 × 270. We present our baseline algorithm and then several sub-algorithms that bring some acceleration. The total acceleration from the first algorithm we used on the CPU to our best algorithm on the GPU is 1 335×. We further distribute individual tasks to thousands of parallel workers running on several European supercomputers. Besides the convergence verification, our program also checks for path records during the convergence test. We found four new path records.

Lean file: `Collatz/Papers/Journal_10_21203_rs_3_rs_3845558_v1.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-g (2026-09-15)
