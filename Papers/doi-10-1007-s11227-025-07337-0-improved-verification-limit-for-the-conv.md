# doi-10-1007-s11227-025-07337-0-improved-verification-limit-for-the-conv

Citation: David Barina, "Improved verification limit for the convergence of the Collatz conjecture", The Journal of Supercomputing, DOI:10.1007/s11227-025-07337-0 [2025].

Authors: David Barina

DOI: [10.1007/s11227-025-07337-0](https://doi.org/10.1007/s11227-025-07337-0)

Year: 2025

Venue: The Journal of Supercomputing

Classification: verification

Abstract:

Abstract This article presents our project, which aims to verify the Collatz conjecture computationally. As a main point of the article, we introduce a new result that pushes the limit for which the conjecture is verified up to $$2^{71}$$ 2 71 . We present our baseline algorithm and then several sub-algorithms that enhance acceleration. The total acceleration from the first algorithm we used on the CPU to our best algorithm on the GPU is $$1\,335\times$$ 1 335 × . We further distribute individual tasks to thousands of parallel workers running on several European supercomputers. Besides the convergence verification, our program also checks for path records during the convergence test. We found four new path records.

Lean file: `Collatz/Papers/Journal_10_1007_s11227_025_07337_0.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-g (2026-09-15)
