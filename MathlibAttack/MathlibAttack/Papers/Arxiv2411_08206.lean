import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Berwyn Hoyt, "Lua API and benchmark design using 3n+1 sequences: Comparing API elegance and raw speed in Redis and YottaDB databases", arXiv:2411.08206 [2024].

Title: Lua API and benchmark design using 3n+1 sequences: Comparing API elegance and raw speed in Redis and YottaDB databases

Abstract (truncated):
Elegance of a database API matters. Frequently, database APIs suit the database designer, rather than the programmer's desire for elegance and efficiency. This article pursues both: firstly, by comparing the Lua APIs for two separate databases, Redis and YottaDB. Secondly, it looks under the API covers at how object orientation can help to retain API efficiency. Finally, it benchmarks both databases using each API to implement a 3n+1 sequence generator (of Collatz Conjecture fame). It covers the eccentricities of the Lua APIs, the databases, and the nifty choice of benchmark tool, presenting benchmark results of each database's unique design.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2411.08206
-/

namespace MathlibAttack.Papers.Arxiv2411_08206

open MathlibAttack.Papers

def citation : String := "Berwyn Hoyt, \"Lua API and benchmark design using 3n+1 sequences: Comparing API elegance and raw speed in Redis and YottaDB databases\", arXiv:2411.08206 [2024]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2411_08206
