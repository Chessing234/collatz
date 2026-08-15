import Collatz.Structure.CycleLength
import Collatz.Structure.CycleExtremes
import Collatz.Search.Sieved

/-!
# Sharpening the cycle-length bound

`Collatz.Structure.CycleLength` bounds every point of a cycle by
`(3^L − 2^L)/(2^L − 3^a)` and compares that against the verified range, giving
`L ≥ 21` for a nontrivial cycle.

Two separate improvements compound here, and both come from *chaining* lemmas
rather than from computing harder.

**First, use both ends of the cycle.**  The original comparison applies the
bound and the verified range to the same point.  But the extremes of a cycle are
linked: `CycleExtremes.two_mul_min_le_cycleMax` gives `M ≥ 2m`.  Applying the
verified range to the *least* point and the size bound to the *greatest* point
therefore doubles the effective constant for free.

**Second, use the sieve to verify.**  `Collatz.Search.Sieved` clears `102 400`
integers by explicitly checking only the `64/1024` of residues that survive the
sieve — a larger range than brute force reaches, at lower cost.

Together these push the exclusion from `L ≤ 20` to **`L ≤ 26`**: no nontrivial
accelerated cycle has length at most twenty-six.

The gain is flat from here until the verified range reaches about `768 000`,
where the exclusion jumps to `L ≤ 31`; that costs roughly forty minutes of
kernel time, which is why this file stops at the efficient point.
-/

namespace Collatz
namespace CycleLengthSharp

open Reach Congruence AccCycle CycleExtremes

/-! ## Every point of a nontrivial cycle is large -/

/-- Every point of a cycle that does not reach `1` lies beyond the verified
range. -/
theorem ge_of_cyclePoint {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n) {i : Nat} :
    102400 ≤ acceleratedOrbit i n := by
  by_cases hlt : acceleratedOrbit i n < 102400
  · exact absurd (reachesOne_of_accOrbit hn
      (Search.reachesOne_of_lt_102400 (acceleratedOrbit_positive hn i) hlt)) hnr
  · omega

/-! ## The doubling gain -/

/-- **The greatest point of a nontrivial cycle is at least twice the verified
range.**  The least point is at least `102 400` because it does not reach `1`,
and the greatest point is at least twice the least. -/
theorem cycleMax_ge {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 204800 ≤ cycleMax n L := by
  obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
  obtain ⟨i, hi⟩ := hm
  have hmge : 102400 ≤ m := by
    have := ge_of_cyclePoint hn hnr (i := i)
    omega
  have hdouble := two_mul_min_le_cycleMax hn h hmin
  omega

/-- **The sharpened exclusion.**  If the size test passes at `200 000` the cycle
cannot exist: its greatest point would have to be both at least `204 800` and at
most `200 000`. -/
theorem not_accCycle_of_check {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n)
    (hcheck : CycleLength.lengthExcluded L 200000 = true) : False := by
  have hge := cycleMax_ge hn h hnr
  have hle := CycleLength.le_of_accCycle (cycleMax_pos hn h) (accIsCycleOf_cycleMax h) hcheck
  omega

/-! ## The verified range of lengths -/

/-- No cycle of length at most `26` can have a greatest point above
`200 000`. -/
theorem check_twentysix : CycleLength.allLengthsExcluded 26 200000 = true := by decide

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

/-- The improvement over the unsharpened bound, stated side by side.  The
extremal lemma and the sieve-accelerated range together move the exclusion from
`20` to `26`. -/
theorem improvement {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 21 ≤ L ∧ 27 ≤ L :=
  ⟨CycleLength.twentyone_le_length_of_nontrivial hn h hnr,
    twentyseven_le_length_of_nontrivial hn h hnr⟩

/-! ## One more length, excluded individually

The sweep `allLengthsExcluded 26` stops at the first length the test fails, but
individual longer lengths can still pass.  Length `28` does: its cycle-point
bound is `164 230`, comfortably inside `200 000`. -/

set_option maxRecDepth 10000 in
/-- Length `28` is excluded individually, even though the sweep stops at `26`. -/
theorem check_twentyeight : CycleLength.lengthExcluded 28 200000 = true := by decide

/-- **A nontrivial cycle does not have length `28`.** -/
theorem length_ne_twentyeight {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : L ≠ 28 := by
  intro hL
  subst hL
  exact not_accCycle_of_check hn h hnr check_twentyeight

/-- The length profile: at least `27`, and never `28`. -/
theorem length_profile {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 27 ≤ L ∧ L ≠ 28 :=
  ⟨twentyseven_le_length_of_nontrivial hn h hnr, length_ne_twentyeight hn h hnr⟩

/-! ## What a cycle would force about `log 2 / log 3`

The size bound can be read backwards.  Rather than asking which lengths it
excludes, ask what a surviving cycle must satisfy — and the answer is a
statement purely about how well `3 ^ a` approximates `2 ^ L` from below. -/

/-- **The approximation constraint.**  A nontrivial cycle of length `L` with `a`
odd steps forces `2 ^ L` and `3 ^ a` to be within a factor `3 ^ L / 204800` of
each other:

`2 ^ L · 204801 ≤ 3 ^ a · 204800 + 3 ^ L`.

Equivalently `2 ^ L − 3 ^ a < 3 ^ L / 204800`.  Since `2 ^ L − 3 ^ a` is a
positive integer, this says `a / L` approximates `log 2 / log 3` far better than
a generic rational of that height could.  Ruling that out for all `L` is exactly
what closes the cycle half, and it is where the elementary argument ends and
transcendence theory would have to begin. -/
theorem approximation_constraint {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) :
    2 ^ L * 204801 ≤ 3 ^ oddCount (cycleMax n L) L * 204800 + 3 ^ L := by
  by_cases hlt : 3 ^ oddCount (cycleMax n L) L * 204800 + 3 ^ L < 2 ^ L * 204801
  · exfalso
    have hbound := CycleLength.le_of_accCycle_of_check (N := 204799)
      (cycleMax_pos hn h) (accIsCycleOf_cycleMax h) (by omega)
    have hge := cycleMax_ge hn h hnr
    omega
  · omega

/-- Both extremes of a nontrivial cycle, bounded below. -/
theorem cycle_extremes_large {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 102400 ≤ n ∧ 204800 ≤ cycleMax n L := by
  refine ⟨?_, cycleMax_ge hn h hnr⟩
  have hz := ge_of_cyclePoint hn hnr (i := 0)
  rw [acceleratedOrbit] at hz
  exact hz

end CycleLengthSharp
end Collatz
