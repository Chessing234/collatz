import Collatz.Structure.CycleLength
import Collatz.Structure.CycleExtremes

/-!
# Sharpening the cycle-length bound

`Collatz.Structure.CycleLength` bounds every point of a cycle by
`(3^L − 2^L)/(2^L − 3^a)` and compares that against the verified range, giving
`L ≥ 21` for a nontrivial cycle.

That comparison is wasteful.  It applies the bound to an arbitrary cycle point
and the verified range to the same point.  But the two extremes of a cycle are
not independent: `CycleExtremes.two_mul_min_le_cycleMax` proves

`M ≥ 2m`

for the greatest and least points.  Applying the *verified range* to the least
point and the *size bound* to the greatest point therefore doubles the effective
constant for free — no extra computation, purely from the extremal lemma.

Combined with verification to `60 000`, this pushes the exclusion from `L ≤ 20`
to **`L ≤ 26`**: no nontrivial accelerated cycle has length at most twenty-six.

The pattern is worth naming, because it is the only place in this project where
two independently proved lemmas combine to beat what either gives alone: a lower
bound on the *small* end of a cycle becomes a lower bound on the *large* end,
where the size bound bites hardest.
-/

namespace Collatz
namespace CycleLengthSharp

open Reach Congruence AccCycle CycleExtremes

/-! ## An extended verified range -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 400000 in
/-- Every `n` with `1 < n ≤ 60000` drops below itself within `150` accelerated
steps. -/
theorem check_drop_60000 : Search.allDropUpTo 60000 150 = true := by decide

/-- Every positive `n ≤ 60000` reaches `1`. -/
theorem reachesOne_of_le_60000 {n : Nat} (hn : 0 < n) (hle : n ≤ 60000) : ReachesOne n :=
  Search.reachesOne_of_allDrop check_drop_60000 n hn hle

/-! ## Every point of a nontrivial cycle is large -/

/-- On a cycle, if one point reaches `1` then so does every point. -/
theorem reachesOne_of_cyclePoint {n : Nat} {i : Nat}
    (hn : 0 < n) (hi : ReachesOne (acceleratedOrbit i n)) : ReachesOne n :=
  reachesOne_of_accOrbit hn hi

/-- Every point of a cycle that does not reach `1` exceeds the verified range. -/
theorem gt_of_cyclePoint {n : Nat} (hn : 0 < n)
    (hnr : ¬ ReachesOne n) {i : Nat} : 60000 < acceleratedOrbit i n := by
  by_cases hle : acceleratedOrbit i n ≤ 60000
  · exact absurd (reachesOne_of_accOrbit hn
      (reachesOne_of_le_60000 (acceleratedOrbit_positive hn i) hle)) hnr
  · omega

/-! ## The doubling gain -/

/-- **The greatest point of a nontrivial cycle exceeds twice the verified
range.**  The least point exceeds `60 000` because it does not reach `1`, and
the greatest point is at least twice the least. -/
theorem cycleMax_gt {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 120000 < cycleMax n L := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmgt : 60000 < m := by
    have := gt_of_cyclePoint hn hnr (i := i)
    omega
  have hdouble := two_mul_min_le_cycleMax hn h hmin
  omega

/-- **The sharpened exclusion.**  If the size test passes at `50 000` then the
cycle cannot exist, because its greatest point would have to be both above
`120 000` and at most `120 000`. -/
theorem not_accCycle_of_check {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n)
    (hcheck : CycleLength.lengthExcluded L 120000 = true) : False := by
  have hgt := cycleMax_gt hn h hnr
  have hle := CycleLength.le_of_accCycle (cycleMax_pos hn h) (accIsCycleOf_cycleMax h) hcheck
  omega

/-! ## The verified range of lengths -/

/-- No cycle of length at most `26` can have a greatest point above
`120 000`. -/
theorem check_twentysix : CycleLength.allLengthsExcluded 26 120000 = true := by decide

/-- **No nontrivial accelerated cycle has length at most twenty-six.** -/
theorem reachesOne_of_short_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hL : L ≤ 26) : ReachesOne n := by
  by_cases hr : ReachesOne n
  · exact hr
  · exact absurd (not_accCycle_of_check hn h hr
      (CycleLength.lengthExcluded_of_all check_twentysix hL)) (by simp)

/-- **A nontrivial accelerated cycle has length at least `27`.** -/
theorem twentyseven_le_length_of_nontrivial {n L : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 27 ≤ L := by
  by_cases hL : L ≤ 26
  · exact absurd (reachesOne_of_short_accCycle hn h hL) hnr
  · omega

/-- The improvement over the unsharpened bound, stated side by side: the
extremal lemma plus the extended range move the exclusion from `20` to `26`. -/
theorem improvement {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 21 ≤ L ∧ 27 ≤ L :=
  ⟨CycleLength.twentyone_le_length_of_nontrivial hn h hnr,
    twentyseven_le_length_of_nontrivial hn h hnr⟩

end CycleLengthSharp
end Collatz
