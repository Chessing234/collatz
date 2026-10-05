import Collatz.Exploration.RankReduction

open Collatz Collatz.Exploration.OrbitFloor Collatz.Exploration.RankReduction

#print axioms collatz_of_ranking
#print axioms hittingTime_spec
#print axioms hittingTime_step
#print axioms ranking_exists_iff_collatz
#print axioms reaches_within_rank
#print axioms canonical_rank_le

-- The canonical rank is specified from actual successful orbits, and is
-- deliberately noncomputable. These checks use the specification, not eval.
example : hittingTime 1 = 0 := hittingTime_one
example : hittingTime 2 = 1 := by
  have h : Converges 2 := ⟨1, by decide⟩
  have ht := hittingTime_step h (by decide)
  rw [step_two, hittingTime_one] at ht
  exact ht
example : hittingTime 4 = 2 := by
  have h2 : hittingTime 2 = 1 := by
    have ht := hittingTime_step (n := 2) ⟨1, by decide⟩ (by decide)
    rw [step_two, hittingTime_one] at ht
    exact ht
  have ht := hittingTime_step (n := 4) ⟨2, by decide⟩ (by decide)
  rw [step_four, h2] at ht
  exact ht
example : ∀ P, Ranking P → 1 ≤ P 2 := by
  intro P hP
  have hs := hP 2 (by decide)
  rw [step_two] at hs
  omega
example : ∀ P, Ranking P → 2 ≤ P 4 := by
  intro P hP
  have h4 := hP 4 (by decide)
  have h2 := hP 2 (by decide)
  rw [step_four] at h4
  rw [step_two] at h2
  omega
