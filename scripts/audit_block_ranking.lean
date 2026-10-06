import Collatz.Exploration.BlockRanking

open Collatz Collatz.Exploration.BlockRanking Collatz.Exploration.RankReduction

#print axioms collatz_of_block_rank
#print axioms reaches_within_block_rank
#print axioms block_rank_lower
#print axioms block_rank_exists_iff_collatz
#print axioms size_block_rank_iff_collatz
#print axioms canonical_block_bound

example : ∀ P, ¬ BoundedBlockRank 0 P := no_zero_horizon
example : ∀ P, Ranking P → BoundedBlockRank 1 P := fun _ h => bounded_block_of_ranking h
example : ∀ H P, BoundedBlockRank H P → BlockRank P := fun _ _ h => block_of_bounded h
example : ∀ n k, orbit k n < n → 0 < k := by
  intro n k hk
  exact lowering_block_positive (P := fun x => x) hk

-- Quantitative cost scales with the chosen horizon; all rank hypotheses remain
-- explicit. The test does not assume that any supplied candidate is valid.
example (P : Nat → Nat) (hP : BoundedBlockRank 3 P) :
    ∃ k, k ≤ 3*P 27 ∧ orbit k 27 = 1 :=
  reaches_within_block_rank hP 27 (by decide)
example (P : Nat → Nat) (hP : BoundedBlockRank 3 P) : 2 ≤ P 27 := by
  have hs := block_rank_lower hP (n := 27) (by decide)
  by_cases h : 2 ≤ P 27
  · exact h
  · have hp : 3*P 27 ≤ 3 := by omega
    have hb : 2^(3*P 27) ≤ 2^3 := Nat.pow_le_pow_right (by decide) hp
    have hv : (2:Nat)^3 = 8 := by decide
    omega
