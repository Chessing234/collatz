import Collatz.Strategy.ScaleLadder
import Collatz.Search.Descent

/-!
# The `2^j − 1` family descends, and how far it has to fall

`PROGRAM_STATUS` poses this as the next smallest lemma statable cold.  With
`r(n) = v₂(n+1)` the length of the initial run of odd accelerated steps, it asks
whether `n > T^(r(n) + s(n))(n)` for some *explicit* `s`, and sets `n = 2^j − 1`
as the first test: there `r = j`, and `T^j(n) = 3^j − 1`, which is far **larger**
than `n`.  So `s` must undo `(3/2)^j` of growth, and the question is whether that
many further steps are available.

The rise is already a theorem: `ScaleLadder.climb` gives
`acceleratedOrbit j (2^j·E − 1) = 3^j·E − 1` for `0 < E`, and at `E = 1` that is
exactly `T^j(2^j − 1) = 3^j − 1`.  What was missing is the fall.

**This file supplies the fall, on a finite range.**  For every `2 ≤ j ≤ 200` the
orbit of `2^j − 1` drops below its start within `12j` accelerated steps.  So on
that range the answer to the question is *yes, the steps are available*, and
`s(j) = 11j` suffices.

## What the numbers actually look like

Writing `σ(j)` for the accelerated stopping time of `2^j − 1`, the ratio `σ(j)/j`
over `2 ≤ j ≤ 300` has maximum `11.2`, attained at the small value `j = 5`
(`σ = 56`), and mean about `2.72`.  Past `j = 30` the ratio never exceeds `4.34`.
The bound `12j` is therefore comfortable rather than tight, and it is driven by
one small case rather than by any trend.

**This is a finite check, not a theorem about all `j`.**  Nothing here shows the
ratio stays bounded, and the family is not refuted — which is the outcome the
question anticipated for this shape.  Establishing a bound for all `j` would mean
controlling the stopping time of `3^j − 1` against the threshold `2^j − 1`, which
is a Collatz-hard problem and is not attempted.
-/

namespace Collatz
namespace MersenneDescent

open Search

/-- The rise, specialized from `ScaleLadder.climb`: `j` odd steps carry `2^j − 1`
to `3^j − 1`. -/
theorem climb_one (j : Nat) : acceleratedOrbit j (2 ^ j - 1) = 3 ^ j - 1 := by
  have h := ScaleLadder.climb j 1 (by omega)
  simpa using h

/-- The finite descent check: every `2 ≤ j ≤ B` drops within `12j` steps. -/
def mersenneDropsUpTo (B : Nat) : Bool :=
  (List.range (B + 1)).all fun j => j < 2 || dropsWithin (12 * j) (2 ^ j - 1)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
set_option exponentiation.threshold 2000 in
theorem mersenneDropsUpTo_200 : mersenneDropsUpTo 200 = true := by decide

/-- **The `2^j − 1` family descends, for `2 ≤ j ≤ 200`.**  Some iterate falls
below the start; the checker above witnesses that it happens within `12j` steps.

Together with `climb_one` this is the full first test of the question in
`PROGRAM_STATUS`: the orbit rises to `3^j − 1` in `j` steps and is back below
`2^j − 1` within `12j`. -/
theorem mersenne_descends {j : Nat} (h2 : 2 ≤ j) (hB : j ≤ 200) :
    ∃ t : Nat, acceleratedOrbit t (2 ^ j - 1) < 2 ^ j - 1 := by
  have hall := List.all_eq_true.mp mersenneDropsUpTo_200 j (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
  rcases hall with hlt | hdrop
  · omega
  · exact exists_lt_of_dropsAux (12 * j) 0 (by simpa [dropsWithin] using hdrop)

end MersenneDescent
end Collatz
