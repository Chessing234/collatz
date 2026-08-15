import Collatz.Search.Descent

/-!
# Stopping times, computed

The *stopping time* `σ(n)` is the least `k ≥ 1` with `T^k(n) < n`.  Terras
(1976) proved that the set of `n` with finite `σ(n)` has natural density one;
Everett (1977) proved the same by a different route.  Neither proof yields the
conjecture, because density one still leaves room for a sparse exceptional set,
and a single counterexample is enough.

This file makes `σ` computable inside Lean, proves the computation sound, and
records the values and counts.  Two things come out of it:

* a table of concrete stopping times, including the two notable spikes
  `σ(27) = 59` and `σ(31) = 56`, which are the reason naive bounds on `σ` fail;
* counting theorems such as `count_le_five_1000`, which exhibit the density
  phenomenon as verified arithmetic rather than as an asymptotic claim.

The counts are the finite shadow of the Terras theorem: of the numbers in
`[2, 1000]`, `874` already stop within five steps and `969` within twenty.
-/

namespace Collatz
namespace Search

open Reach

/-! ## Computing the stopping time -/

/-- `sigmaAux n fuel k cur` searches for the first drop below `n`, having
already taken `k` steps to reach `cur`.  It returns `0` when the fuel runs
out. -/
def sigmaAux (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, k, cur =>
      let next := acceleratedStep cur
      if next < n then k + 1 else sigmaAux n fuel (k + 1) next

/-- `sigma fuel n` is the stopping time of `n`, or `0` if none is found within
`fuel` steps. -/
def sigma (fuel n : Nat) : Nat := sigmaAux n fuel 0 n

/-- Unfolding the search. -/
theorem sigmaAux_succ (n fuel k cur : Nat) :
    sigmaAux n (fuel + 1) k cur =
      (if acceleratedStep cur < n then k + 1
       else sigmaAux n fuel (k + 1) (acceleratedStep cur)) := rfl

/-- The exhausted search returns zero. -/
@[simp] theorem sigmaAux_zero (n k cur : Nat) : sigmaAux n 0 k cur = 0 := rfl

/-- **Soundness of the stopping-time computation.**  A nonzero result really is
a step count at which the orbit drops. -/
theorem accOrbit_lt_of_sigmaAux {n : Nat} : ∀ (fuel k j : Nat),
    acceleratedOrbit j n = acceleratedOrbit j n →
    ∀ cur : Nat, cur = acceleratedOrbit j n →
    sigmaAux n fuel k cur ≠ 0 →
    ∃ i : Nat, 0 < i ∧ acceleratedOrbit i n < n := by
  intro fuel
  induction fuel with
  | zero => intro k j _ cur _ h; simp at h
  | succ fuel ih =>
    intro k j _ cur hcur h
    rw [hcur, sigmaAux_succ] at h
    have hnext : acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit (j + 1) n :=
      (acceleratedOrbit_succ_step j n).symm
    by_cases hlt : acceleratedStep (acceleratedOrbit j n) < n
    · exact ⟨j + 1, by omega, by rw [← hnext]; exact hlt⟩
    · rw [if_neg hlt] at h
      exact ih (k + 1) (j + 1) rfl _ hnext h

/-- A nonzero computed stopping time certifies a genuine drop. -/
theorem exists_drop_of_sigma_ne_zero {fuel n : Nat} (h : sigma fuel n ≠ 0) :
    ∃ i : Nat, 0 < i ∧ acceleratedOrbit i n < n := by
  refine accOrbit_lt_of_sigmaAux fuel 0 0 rfl n ?_ h
  rw [acceleratedOrbit]

/-- A nonzero computed stopping time gives the drop used by descent
arguments. -/
theorem accOrbit_lt_of_sigma {fuel n : Nat} (h : sigma fuel n ≠ 0) :
    ∃ i : Nat, acceleratedOrbit i n < n := by
  obtain ⟨i, _, hi⟩ := exists_drop_of_sigma_ne_zero h
  exact ⟨i, hi⟩

/-! ## The table

Every entry is a closed kernel computation. -/

theorem sigma_two : sigma 100 2 = 1 := by decide
theorem sigma_three : sigma 100 3 = 4 := by decide
theorem sigma_four : sigma 100 4 = 1 := by decide
theorem sigma_five : sigma 100 5 = 2 := by decide
theorem sigma_six : sigma 100 6 = 1 := by decide
theorem sigma_seven : sigma 100 7 = 7 := by decide
theorem sigma_eight : sigma 100 8 = 1 := by decide
theorem sigma_nine : sigma 100 9 = 2 := by decide
theorem sigma_ten : sigma 100 10 = 1 := by decide
theorem sigma_eleven : sigma 100 11 = 5 := by decide
theorem sigma_twelve : sigma 100 12 = 1 := by decide
theorem sigma_thirteen : sigma 100 13 = 2 := by decide
theorem sigma_fourteen : sigma 100 14 = 1 := by decide
theorem sigma_fifteen : sigma 100 15 = 7 := by decide
theorem sigma_sixteen : sigma 100 16 = 1 := by decide
theorem sigma_seventeen : sigma 100 17 = 2 := by decide
theorem sigma_eighteen : sigma 100 18 = 1 := by decide
theorem sigma_nineteen : sigma 100 19 = 4 := by decide
theorem sigma_twenty : sigma 100 20 = 1 := by decide
theorem sigma_twentyone : sigma 100 21 = 2 := by decide
theorem sigma_twentytwo : sigma 100 22 = 1 := by decide
theorem sigma_twentythree : sigma 100 23 = 5 := by decide
theorem sigma_twentyfour : sigma 100 24 = 1 := by decide
theorem sigma_twentyfive : sigma 100 25 = 2 := by decide
theorem sigma_twentysix : sigma 100 26 = 1 := by decide

set_option maxRecDepth 4000 in
/-- The first spike: `27` needs `59` accelerated steps before it drops. -/
theorem sigma_twentyseven : sigma 100 27 = 59 := by decide

theorem sigma_twentyeight : sigma 100 28 = 1 := by decide
theorem sigma_twentynine : sigma 100 29 = 2 := by decide
theorem sigma_thirty : sigma 100 30 = 1 := by decide

set_option maxRecDepth 4000 in
/-- The second spike: `31` needs `56` steps. -/
theorem sigma_thirtyone : sigma 100 31 = 56 := by decide

theorem sigma_thirtytwo : sigma 100 32 = 1 := by decide
theorem sigma_thirtythree : sigma 100 33 = 2 := by decide
theorem sigma_thirtyfour : sigma 100 34 = 1 := by decide
theorem sigma_thirtyfive : sigma 100 35 = 4 := by decide
theorem sigma_thirtysix : sigma 100 36 = 1 := by decide
theorem sigma_thirtyseven : sigma 100 37 = 2 := by decide
theorem sigma_thirtyeight : sigma 100 38 = 1 := by decide
theorem sigma_thirtynine : sigma 100 39 = 8 := by decide
theorem sigma_forty : sigma 100 40 = 1 := by decide
theorem sigma_fortyone : sigma 100 41 = 2 := by decide

/-- Every even number has stopping time exactly one. -/
theorem sigma_eq_one_of_even {n : Nat} (hn : 1 < n) (he : n % 2 = 0) (fuel : Nat) :
    sigma (fuel + 1) n = 1 := by
  have hstep : acceleratedStep n = n / 2 := by
    rw [acceleratedStep, if_pos he]
  rw [sigma, sigmaAux_succ, hstep, if_pos (by omega)]

/-! ## Counting: the density phenomenon, finitely -/

/-- `countStopBy N B` counts the `n` in `[2, N]` whose stopping time is at most
`B`. -/
def countStopBy : Nat → Nat → Nat
  | 0, _ => 0
  | 1, _ => 0
  | m + 2, B => (if sigma B (m + 2) ≠ 0 then 1 else 0) + countStopBy (m + 1) B

/-- Unfolding the count. -/
theorem countStopBy_succ (m B : Nat) :
    countStopBy (m + 2) B = (if sigma B (m + 2) ≠ 0 then 1 else 0) + countStopBy (m + 1) B :=
  rfl

set_option maxRecDepth 20000 in
/-- Half of `[2, 1000]` stops in a single step: exactly the even numbers. -/
theorem count_le_one_1000 : countStopBy 1000 1 = 500 := by decide

set_option maxRecDepth 20000 in
/-- Within two steps, `749` of the `999` numbers in `[2, 1000]` have stopped. -/
theorem count_le_two_1000 : countStopBy 1000 2 = 749 := by decide

set_option maxRecDepth 20000 in
/-- Within five steps, `874`. -/
theorem count_le_five_1000 : countStopBy 1000 5 = 874 := by decide

set_option maxRecDepth 20000 in
/-- Within twenty steps, `969` — the tail is thin but nonempty, which is
precisely why density arguments stop short of the conjecture. -/
theorem count_le_twenty_1000 : countStopBy 1000 20 = 969 := by decide

set_option maxRecDepth 40000 in
/-- Within one hundred steps every number in `[2, 1000]` has stopped, so the
exceptional set is empty at this scale. -/
theorem count_le_hundred_1000 : countStopBy 1000 100 = 999 := by decide

end Search
end Collatz
