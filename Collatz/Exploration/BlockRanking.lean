import Collatz.Exploration.RankGrowth
import Collatz.Exploration.TimeChange

/-!
# Variable-block rankings and their quantitative cost

Immediate strict decrease is stronger than a rank drop after a chosen block.
Here the block length may depend on the input, and the orbit can grow within
the block. Well-founded induction on the rank still proves convergence.
A uniform block horizon H yields the explicit standard hitting bound H*P(n).

The assumptions are stated as propositions and are never supplied by fiat.
For P(n)=n the unrestricted version is universal descent itself; it is therefore
equivalent to Collatz, rather than an easier auxiliary theorem.
The modular obstruction applies separately to bounded accelerated lookahead.
-/
namespace Collatz.Exploration.BlockRanking

open OrbitFloor RankReduction RankGrowth TimeChange

/-- Some standard block lowers the rank at each nontrivial state. -/
def BlockRank (P : Nat → Nat) : Prop :=
  ∀ n, 1 < n → ∃ k, P (orbit k n) < P n

/-- A block-rank certificate with a uniform upper bound on its block length. -/
def BoundedBlockRank (H : Nat) (P : Nat → Nat) : Prop :=
  ∀ n, 1 < n → ∃ k, k ≤ H ∧ P (orbit k n) < P n

/-- Any successful lowering block automatically has positive length. -/
theorem lowering_block_positive {n k : Nat} {P : Nat → Nat}
    (hk : P (orbit k n) < P n) : 0 < k := by
  by_cases hz : k = 0
  · rw [hz, orbit_zero_steps] at hk
    omega
  · omega

/-- An immediate rank is a block rank with unit horizon. -/
theorem bounded_block_of_ranking {P : Nat → Nat} (hP : Ranking P) :
    BoundedBlockRank 1 P := by
  intro n hn
  exact ⟨1, Nat.le_refl _, hP n hn⟩

/-- Forgetting the horizon yields the unrestricted block-rank assumption. -/
theorem block_of_bounded {H : Nat} {P : Nat → Nat}
    (hP : BoundedBlockRank H P) : BlockRank P := by
  intro n hn
  obtain ⟨k, _, hk⟩ := hP n hn
  exact ⟨k, hk⟩

/-- Rank induction allows growth of the input and any number of intervening steps. -/
theorem collatz_of_block_rank {P : Nat → Nat} (hP : BlockRank P) : CollatzConjecture := by
  have h : ∀ r n, P n = r → 0 < n → Converges n := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro n hr hp
      by_cases hn : n = 1
      · exact ⟨0, hn⟩
      · obtain ⟨k, hk⟩ := hP n (by omega)
        have hdrop : P (orbit k n) < r := by rw [← hr]; exact hk
        obtain ⟨j, hj⟩ := ih _ hdrop (orbit k n) rfl (orbit_positive hp k)
        exact ⟨j+k, by rw [orbit_add, hj]⟩
  intro n hn
  exact h (P n) n rfl hn

/-- A bounded block rank pays at most H standard steps per rank unit. -/
theorem reaches_within_block_rank {H : Nat} {P : Nat → Nat}
    (hP : BoundedBlockRank H P) :
    ∀ n, 0 < n → ∃ k, k ≤ H*P n ∧ orbit k n = 1 := by
  have h : ∀ r n, P n = r → 0 < n → ∃ k, k ≤ H*r ∧ orbit k n = 1 := by
    intro r
    induction r using Nat.strongRecOn with
    | _ r ih =>
      intro n hr hp
      by_cases hn : n = 1
      · exact ⟨0, Nat.zero_le _, hn⟩
      · obtain ⟨k, htime, hdrop⟩ := hP n (by omega)
        have hd : P (orbit k n) < r := by rw [← hr]; exact hdrop
        obtain ⟨j, hj, he⟩ := ih _ hd (orbit k n) rfl (orbit_positive hp k)
        have hmul : H*(P (orbit k n)+1) ≤ H*r :=
          Nat.mul_le_mul_left H (by omega)
        rw [Nat.mul_add, Nat.mul_one] at hmul
        exact ⟨j+k, by omega, by rw [orbit_add, he]⟩
  intro n hn
  exact h (P n) n rfl hn

/-- Any bounded block rank still has to account for dyadic input size. -/
theorem block_rank_lower {H : Nat} {P : Nat → Nat}
    (hP : BoundedBlockRank H P) {n : Nat} (hn : 0 < n) : n ≤ 2^(H*P n) := by
  obtain ⟨k, hk, he⟩ := reaches_within_block_rank hP n hn
  exact Nat.le_trans (successful_time_lower he)
    (Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) hk)

/-- No zero-horizon global block rank exists. -/
theorem no_zero_horizon (P : Nat → Nat) : ¬ BoundedBlockRank 0 P := by
  intro hP
  obtain ⟨k, hk, hd⟩ := hP 2 (by decide)
  have hz : k = 0 := by omega
  rw [hz, orbit_zero_steps] at hd
  omega

/-- Existence of an arbitrary block rank is another exact form of Collatz. -/
theorem block_rank_exists_iff_collatz : (∃ P, BlockRank P) ↔ CollatzConjecture := by
  constructor
  · rintro ⟨P, hP⟩
    exact collatz_of_block_rank hP
  · intro hc
    exact ⟨hittingTime, block_of_bounded (bounded_block_of_ranking (hittingTime_ranking hc))⟩

/-- Size as a block rank is precisely universal standard descent. -/
theorem size_block_rank_iff_collatz : BlockRank (fun n => n) ↔ CollatzConjecture := by
  constructor
  · exact collatz_of_block_rank
  · intro hc n hn
    obtain ⟨k, hk⟩ := hc n (by omega)
    exact ⟨k, by dsimp only; rw [hk]; exact hn⟩

/-- The exact first hitting rank is no larger than the block-rank cost. -/
theorem canonical_block_bound {H : Nat} {P : Nat → Nat}
    (hP : BoundedBlockRank H P) {n : Nat} (hn : 0 < n) :
    hittingTime n ≤ H*P n := by
  obtain ⟨k, hk, he⟩ := reaches_within_block_rank hP n hn
  exact Nat.le_trans ((hittingTime_spec ⟨k, he⟩).2 k he) hk

end Collatz.Exploration.BlockRanking
