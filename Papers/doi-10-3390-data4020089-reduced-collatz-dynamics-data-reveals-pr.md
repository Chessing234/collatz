# doi-10-3390-data4020089-reduced-collatz-dynamics-data-reveals-pr

Citation: Wei Ren, "Reduced Collatz Dynamics Data Reveals Properties for the Future Proof of Collatz Conjecture", Data, DOI:10.3390/data4020089 [2019].

Authors: Wei Ren

DOI: [10.3390/data4020089](https://doi.org/10.3390/data4020089)

Year: 2019

Venue: Data

Classification: verification

Abstract:

Collatz conjecture is also known as 3X + 1 conjecture. For verifying the conjecture, we designed an algorithm that can output reduced dynamics (occurred 3 × x + 1 or x/2 computations from a starting integer to the first integer smaller than the starting integer) and original dynamics of integers (from a starting integer to 1). Especially, the starting integer has no upper bound. That is, extremely large integers with length of about 100,000 bits, e.g., 2100000 − 1, can be verified for Collatz conjecture, which is much larger than current upper bound (about 260). We analyze the properties of those data (e.g., reduced dynamics) and discover the following laws; reduced dynamics is periodic and the period is the length of its reduced dynamics; the count of x/2 equals to minimal integer that...

Lean file: `Collatz/Papers/Journal_10_3390_data4020089.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-f (2026-09-15)
