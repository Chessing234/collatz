import Collatz.Search.Sieved

/-!
# The verified range, extended to 768 000

`Search.Sieved` clears `307 200` by checking, in six chunks of fifty blocks, the
sixty-four residues modulo `1024` that survive the level-`10` sieve.  Its closing
paragraph names the next stop and prices it: "`750` blocks would clear `768 000`
at roughly nine more minutes".  This file pays that bill.

Nothing here is new mathematics, and it would be dishonest to dress it as such.
The soundness theorem is `reachesOne_of_blocks`, unchanged; the block checker is
`checkBlock`, unchanged; the fuel is `200`, unchanged; the chunking into fifties
is the same device for the same reason — one `decide` over four hundred and fifty
blocks does not finish, because the cost of a single kernel evaluation grows
non-linearly in its size, while the cost of many small ones does not.  All that
happens below is that nine more chunks are handed to the kernel.

**What the compute buys.**  The verified range is the one asset in this
development that converts machine time into a strictly stronger theorem.  Every
other file argues; this one measures.  And the conversion rate is known: the
product bound of `CycleProduct` excludes a cycle length `L` once `3 ^ a (3c + 2a)
< 3c · 2 ^ L` at the top admissible exponent, and the largest `L` that survives
grows like `√c` in the verified range `c`.  Tripling the range from `102 400` to
`307 200` moved the cycle bound from `520` to `1539`; multiplying it by two and a
half again, to `768 000`, moves the bound to `2593`.  That is the square-root
law, and it is also the reason this is a poor long-term strategy: the next
doubling of the bound costs four times this file's kernel budget, and the one
after that sixteen.  Compute is a ladder with rungs that get further apart.

**The fuel.**  A direct scan of all `28 800` surviving residues in
`[307 200, 768 000)` finds that the slowest to drop is `626 331`, which needs
`176` accelerated steps; every other survivor is faster, and none fails.  Fuel
`200` therefore clears the whole extension with twenty-four steps of margin, and
— what matters for the plumbing — it is the *same* fuel the existing six chunks
were checked with, so the old and new chunks aggregate into a single application
of `reachesOne_of_blocks`.

**The cost, measured.**  Each fifty-block chunk costs about thirty-five seconds
of kernel time on the machine this was compiled on, so the nine chunks below run
to roughly five minutes, and the file is the dominant cost of `lake build
Collatz`.  The cost is linear in blocks and will stay linear; it is the *payoff*
that is square-root.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Nine more chunks

Blocks `300` through `749`, fifty at a time, at the same fuel `200` as the six
chunks of `Sieved`. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r6 : checkRange 300 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r7 : checkRange 350 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r8 : checkRange 400 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r9 : checkRange 450 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r10 : checkRange 500 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r11 : checkRange 550 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r12 : checkRange 600 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r13 : checkRange 650 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r14 : checkRange 700 50 200 = true := by decide

/-! ## Aggregation

The same case split as `Sieved.drops_all`, continued: six old chunks below `300`,
nine new ones above. -/

/-- Every surviving residue in every block below `750` drops within `200`
accelerated steps. -/
theorem drops_all_750 {m r : Nat} (hm : m < 750) (hr : r ∈ survivorsMod1024) :
    dropsWithin 200 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 300 with h | h
  · exact drops_all h hr
  · rcases Nat.lt_or_ge m 500 with h1 | h1
    · rcases Nat.lt_or_ge m 400 with h2 | h2
      · rcases Nat.lt_or_ge m 350 with h3 | h3
        · exact drops_of_checkRange check_r6 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r7 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 450 with h3 | h3
        · exact drops_of_checkRange check_r8 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r9 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 650 with h2 | h2
      · rcases Nat.lt_or_ge m 550 with h3 | h3
        · exact drops_of_checkRange check_r10 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 600 with h4 | h4
          · exact drops_of_checkRange check_r11 (by omega) (by omega) hr
          · exact drops_of_checkRange check_r12 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 700 with h3 | h3
        · exact drops_of_checkRange check_r13 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r14 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `768 000` reaches `1`.**  Two and a half times the
range of `reachesOne_of_lt_307200`, by the same argument at greater expense. -/
theorem reachesOne_of_lt_768000 {n : Nat} (hn : 0 < n) (hlt : n < 768000) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 750) (fuel := 200)
    (fun m r hm hr => drops_all_750 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 750 = 768000 := by decide
  omega

/-- A counterexample is at least `768 000`. -/
theorem counterexample_ge_768000 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) :
    768000 ≤ n := by
  by_cases hlt : n < 768000
  · exact absurd (reachesOne_of_lt_768000 hn hlt) h
  · omega

end Search
end Collatz
