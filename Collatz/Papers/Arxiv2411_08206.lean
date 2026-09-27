import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Berwyn Hoyt, "Lua API and benchmark design using 3n+1 sequences: Comparing API elegance and raw speed in Redis and YottaDB databases", arXiv:2411.08206 [2024].

Title: Lua API and benchmark design using 3n+1 sequences: Comparing API elegance and raw speed in Redis and YottaDB databases

Abstract (from OpenAlex metadata, truncated):
Elegance of a database API matters. Frequently, database APIs suit the database designer, rather than the programmer's desire for elegance and efficiency. This article pursues both: firstly, by comparing the Lua APIs for two separate databases, Redis and YottaDB. Secondly, it looks under the API covers at how object orientation can help to retain API efficiency. Finally, it benchmarks both databases using each API to implement a 3n+1 sequence generator (of Collatz Conjecture fame). It covers the eccentricities of the Lua APIs, the databases, and the nifty choice of benchmark tool, presenting benchmark results of each database's unique design.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2411.08206
-/

namespace Collatz.Papers.Arxiv2411_08206

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Berwyn Hoyt, \"Lua API and benchmark design using 3n+1 sequences: Comparing API elegance and raw speed in Redis and YottaDB databases\", arXiv:2411.08206 [2024]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2411_08206
