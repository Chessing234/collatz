# doi-10-1109-hpcc-smartcity-dss-2019-00382-how-to-fast-verify-collatz-conjecture-by

Citation: Wei Ren and Ruiyang Xiao, "How to Fast Verify Collatz Conjecture by Automata", 2019 IEEE 21st International Conference on High Performance Computing and Communications; IEEE 17th International Conference on Smart City; IEEE 5th International Conference on Data Science and Systems (HPCC/SmartCity/DSS), DOI:10.1109/hpcc/smartcity/dss.2019.00382 [2019].

Authors: Wei Ren, Ruiyang Xiao

DOI: [10.1109/hpcc/smartcity/dss.2019.00382](https://doi.org/10.1109/hpcc/smartcity/dss.2019.00382)

Year: 2019

Venue: 2019 IEEE 21st International Conference on High Performance Computing and Communications; IEEE 17th International Conference on Smart City; IEEE 5th International Conference on Data Science and Systems (HPCC/SmartCity/DSS)

Classification: verification

Abstract:

To verify Collatz conjecture for a given integer, we need to justify whether or not the given starting number goes to 1 finally. Current method computes 3*x+1 and x/2 one by one. In this paper, we propose an automata-based algorithm to compute the process in a batch with m steps - (3*x+1)2 or x/2. We also propose reduced Collatz conjecture and we prove it is equivalent to Collazt conjecture. We also point out that original dynamics is the combination of reduced dynamics. (Original dynamics is a serial of occurred 3*x+1 and x/2 computation in the process from a starting number to 1; Reduced dynamics is a serial of occurred 3*x+1 and x/2 computation in the process from a starting number to the first transformed number that is less than the starting number.) We study the properties of...

Lean file: `Collatz/Papers/Journal_10_1109_hpcc_smartcity_dss_2019_00382.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-g (2026-09-15)
