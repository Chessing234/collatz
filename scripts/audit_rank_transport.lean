import Collatz.Exploration.RankTransport

open Collatz Collatz.Exploration.RankReduction Collatz.Exploration.RankTransport

#print axioms accelerated_of_standard
#print axioms standard_of_accelerated
#print axioms ranking_exists_iff
#print axioms acc_ranking_exists_iff_collatz
#print axioms no_residue_monotone_standard
#print axioms standard_hitting_bound

-- The lift is a computable formula; validity remains conditional on AccRanking.
example : liftRank (fun n => n) 1 = 2 := by decide
example : liftRank (fun n => n) 2 = 3 := by decide
example : liftRank (fun n => n) 3 = 6 := by decide
example : liftRank (fun n => n) 4 = 5 := by decide
example : liftRank (fun n => n) 10 = 11 := by decide
example : ¬ AccRanking (fun _ => 0) := by
  intro h
  have hs := h 2 (by decide)
  dsimp only at hs
  omega
example : ¬ Ranking (fun n => n) := by
  exact no_residue_monotone_standard (M := 1) (by decide)
    (fun _ _ _ h => h)
example : ∀ P, AccRanking P → liftRank P 2 > liftRank P 1 := by
  intro P hP
  have h := standard_of_accelerated hP 2 (by decide)
  rw [step_two] at h
  exact h
example (hc : CollatzConjecture) : Ranking (liftRank hittingTime) :=
  standard_of_accelerated (accelerated_of_standard (hittingTime_ranking hc))
