# arxiv-2411-08206-lua-api-and-benchmark-design-using-3n-1-sequences-comparing-

Citation: Berwyn Hoyt, "Lua API and benchmark design using 3n+1 sequences: Comparing API elegance and raw speed in Redis and YottaDB databases", arXiv:2411.08206 [2024].

Authors: Berwyn Hoyt

arXiv: [2411.08206](https://arxiv.org/abs/2411.08206)

Year: 2024

Classification: structural

Abstract:

Elegance of a database API matters. Frequently, database APIs suit the database designer, rather than the programmer's desire for elegance and efficiency. This article pursues both: firstly, by comparing the Lua APIs for two separate databases, Redis and YottaDB. Secondly, it looks under the API covers at how object orientation can help to retain API efficiency. Finally, it benchmarks both databases using each API to implement a 3n+1 sequence generator (of Collatz Conjecture fame). It covers the eccentricities of the Lua APIs, the databases, and the nifty choice of benchmark tool, presenting benchmark results of each database's unique design.

Lean file: `Collatz/Papers/Arxiv2411_08206.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
