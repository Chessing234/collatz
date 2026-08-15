import Collatz.Structure.AffineBound
import Collatz.Structure.AccCycle
import Collatz.Search.Descent

/-!
# A lower bound on the length of a nontrivial cycle

Every point `n` of an accelerated cycle of length `L` satisfies

`2 ^ L · n = 3 ^ a · n + b`,   `a = a(n,L)`,   `b + 2 ^ L ≤ 3 ^ L`

by `AffineBound.affine_of_cycle`.  Since `3 ^ a < 2 ^ L` on a cycle, this pins
`n` down completely:

`(2 ^ L − 3 ^ a) · n = b ≤ 3 ^ L − 2 ^ L`,   so   `n ≤ (3 ^ L − 2 ^ L)/(2 ^ L − 3 ^ a)`.

**Every point of a short cycle is small.**  Combined with the verified range —
everything up to `10 000` reaches `1` — this rules out short cycles outright.

The bound is only useful when `2 ^ L − 3 ^ a` is not tiny, and how small that
difference can be is exactly the question of how well `log 2 / log 3` is
approximated by rationals.  That is why this method stalls: pushing much past
`L = 20` needs transcendence theory rather than arithmetic.  Within its range it
is completely effective, and the range grows with the verified initial segment.

The exported result is `no_short_accCycle`: **a cycle of the accelerated map of
length at most `20` consists of numbers that reach `1`**, so any nontrivial
cycle has length at least `21`.
-/

namespace Collatz
namespace CycleLength

open Reach Congruence AccCycle

/-! ## The exclusion test -/

/-- `lengthExcluded L N` checks that no cycle of length `L` can have a point
above `N`.  For each possible odd-step count `a` it verifies the inequality
`3 ^ a (N+1) + 3 ^ L < 2 ^ L (N+2)`, which says that a point of size `N + 1`
would already violate the affine bound. -/
def lengthExcluded (L N : Nat) : Bool :=
  (List.range L).all fun a =>
    decide (2 ^ L ≤ 3 ^ a) || decide (3 ^ a * (N + 1) + 3 ^ L < 2 ^ L * (N + 2))

/-- `allLengthsExcluded M N` runs the test for every length up to `M`. -/
def allLengthsExcluded (M N : Nat) : Bool :=
  (List.range (M + 1)).all fun L => lengthExcluded L N

/-- Reading a single length out of the sweep. -/
theorem lengthExcluded_of_all {M N L : Nat} (h : allLengthsExcluded M N = true)
    (hL : L ≤ M) : lengthExcluded L N = true := by
  rw [allLengthsExcluded, List.all_eq_true] at h
  exact h L (List.mem_range.mpr (by omega))

/-- Reading a single odd-step count out of the test. -/
theorem check_of_lengthExcluded {L N a : Nat} (h : lengthExcluded L N = true)
    (ha : a < L) (hlt : 3 ^ a < 2 ^ L) :
    3 ^ a * (N + 1) + 3 ^ L < 2 ^ L * (N + 2) := by
  rw [lengthExcluded, List.all_eq_true] at h
  have hmem := h a (List.mem_range.mpr ha)
  have hne : ¬ (2 ^ L ≤ 3 ^ a) := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hmem
  rcases hmem with hc | hc
  · exact absurd hc hne
  · exact hc

/-! ## Every point of a short cycle is small -/

/-- **The size bound.**  If the exclusion test passes for `(L, N)`, then every
point of an accelerated cycle of length `L` is at most `N`. -/
theorem le_of_accCycle {n L N : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hcheck : lengthExcluded L N = true) : n ≤ N := by
  -- the cycle equation with a bounded constant
  obtain ⟨b, heq, hb⟩ := AffineBound.affine_of_cycle h.2
  -- the counting inequality forces `3 ^ a < 2 ^ L` and `a < L`
  have hlt : 3 ^ oddCount n L < 2 ^ L :=
    Cycle.two_pow_gt_three_pow_of_accCycle hn h.1 h.2
  have ha : oddCount n L < L := Cycle.oddCount_lt_length_of_accCycle hn h.1 h.2
  have hchk := check_of_lengthExcluded hcheck ha hlt
  -- suppose the point were larger than `N`
  by_cases hle : n ≤ N
  · exact hle
  · exfalso
    have hge : N + 1 ≤ n := by omega
    -- write `n = (N + 1) + t` and expand both sides of the cycle equation
    have ht : n = (N + 1) + (n - (N + 1)) := by omega
    have hexp2 : 2 ^ L * ((N + 1) + (n - (N + 1)))
        = 2 ^ L * (N + 1) + 2 ^ L * (n - (N + 1)) := Nat.mul_add _ _ _
    have hexp3 : 3 ^ oddCount n L * ((N + 1) + (n - (N + 1)))
        = 3 ^ oddCount n L * (N + 1) + 3 ^ oddCount n L * (n - (N + 1)) := Nat.mul_add _ _ _
    rw [← ht] at hexp2 hexp3
    -- the shifted parts compare because `3 ^ a < 2 ^ L`
    have hshift : 3 ^ oddCount n L * (n - (N + 1)) ≤ 2 ^ L * (n - (N + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    -- and the base parts are governed by the exclusion test
    have hbase : 2 ^ L * (N + 2) = 2 ^ L * (N + 1) + 2 ^ L := by
      have hN : N + 2 = (N + 1) + 1 := by omega
      rw [hN, Nat.mul_succ]
    omega

/-- With the verified initial segment, a cycle of an excluded length consists of
numbers that reach `1`. -/
theorem reachesOne_of_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hcheck : lengthExcluded L 10000 = true) : ReachesOne n :=
  Search.reachesOne_of_le_10000 hn (le_of_accCycle hn h hcheck)

/-! ## The verified range

A single kernel computation clears every length up to twenty. -/

/-- No accelerated cycle of length at most `20` can contain a point above
`10 000`. -/
theorem check_twenty : allLengthsExcluded 20 10000 = true := by decide

/-- **No short cycles.**  Every point of an accelerated cycle of length at most
`20` reaches `1`, so the only such cycle is the trivial one. -/
theorem no_short_accCycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hL : L ≤ 20) : ReachesOne n :=
  reachesOne_of_accCycle hn h (lengthExcluded_of_all check_twenty hL)

/-- **A nontrivial accelerated cycle has length at least `21`.** -/
theorem twentyone_le_length_of_nontrivial {n L : Nat} (hn : 0 < n)
    (h : AccIsCycleOf n L) (hnr : ¬ ReachesOne n) : 21 ≤ L := by
  by_cases hL : L ≤ 20
  · exact absurd (no_short_accCycle hn h hL) hnr
  · omega

/-- Restated for the size of the cycle's points: a point of a nontrivial cycle
of length `L ≤ 20` cannot exist. -/
theorem no_nontrivial_short_cycle {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hL : L ≤ 20) : 10000 < n → False := by
  intro hgt
  have := le_of_accCycle hn h (lengthExcluded_of_all check_twenty hL)
  omega

end CycleLength
end Collatz
