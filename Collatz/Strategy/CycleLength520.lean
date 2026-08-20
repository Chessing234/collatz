import Collatz.Strategy.CycleProduct

/-!
# Every nontrivial cycle has length at least 520

`CycleProduct` proves two things that were never put together.

`no_cycle_of_excludedLength` says a cycle is impossible at any length passing a
decidable test, and `excludedLength_of_lt` says the test passes for every
`L < 520` at floor `307 200`.  Both were leaves: nothing in the development used
either, and `Master.cycle_profile` still recorded the older bound `27 ≤ L`.

This file discharges the hypotheses and closes the gap.  The only work is
transport: the exclusion test wants its hypotheses at the cycle's *least* point,
while the size bound and the cycle equation are stated at an arbitrary point of
the orbit.

* `AccCycle.exists_accCycleMin` produces the least value `m = T^i(n)`;
* `m` is itself a cycle of the same length, since `T^L(m) = T^(i+L)(n) = T^i(n)`;
* `VerifiedSharp.ge_verified_sharp` bounds *every* orbit point below by
  `307 200`, and every point of `m`'s orbit is a point of `n`'s;
* the smallness hypothesis `2 · a ≤ 3 · 307 200` is free, because `a ≤ L < 520`.

The result is `520 ≤ L` (`length_ge_520`), a factor of nineteen over the
previous bound, obtained with no new mathematics at all — only by composing two
theorems that were already kernel-checked.

The ceiling is a build cost, not a limit of the method: exact integer
computation puts the first surviving pair at `(L, a) = (1539, 971)`, so the same
argument reaches `L ≥ 1539` and stops there, where `2 ^ L / 3 ^ a` comes close
enough to one that the product bound goes silent.
-/

namespace Collatz
namespace CycleLength520

open Reach Congruence AccCycle CycleExtremes NeverDrops CycleProduct

/-- **A nontrivial accelerated cycle has length at least `520`.** -/
theorem length_ge_520 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 520 ≤ L := by
  rcases Nat.lt_or_ge L 520 with hL | hL
  · exfalso
    obtain ⟨m, hm, _hmin⟩ := exists_accCycleMin n
    obtain ⟨i, hi⟩ := hm
    have hmpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    -- every point of `m`'s orbit is a point of `n`'s orbit
    have htrans : ∀ k : Nat, acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
      intro k
      rw [← hi, acceleratedOrbit_add k i n]
    have hc : ∀ k : Nat, 307200 ≤ acceleratedOrbit k m := by
      intro k
      exact VerifiedSharp.ge_verified_sharp hn hnr ⟨k + i, (htrans k).symm⟩
    -- `m` is a cycle of the same length
    have hcyc : acceleratedOrbit L m = m := by
      rw [htrans L, Nat.add_comm L i, ← acceleratedOrbit_add i L n, h.2, hi]
    have hlt' : oddCount m L < L := Cycle.oddCount_lt_length_of_accCycle hmpos h.1 hcyc
    have hle : oddCount m L ≤ L := Nat.le_of_lt hlt'
    have hsmall : 2 * oddCount m L ≤ 3 * 307200 := by omega
    have hlt : 3 ^ oddCount m L < 2 ^ L :=
      Cycle.two_pow_gt_three_pow_of_accCycle hmpos h.1 hcyc
    exact no_cycle_of_excludedLength hmpos (by omega) hc hcyc hsmall hle hlt
      (excludedLength_of_lt hL)
  · exact hL

/-- Restated for a counterexample that is periodic. -/
theorem length_ge_520_of_periodic {n : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (h : AccPeriodic n) : ∃ L : Nat, AccIsCycleOf n L ∧ 520 ≤ L := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, hL, length_ge_520 hn hL hnr⟩

/-- **The sharpened cycle profile.**  Length at least `520`, an odd-step count
strictly between `0` and `L`, and the near-approximation `3 ^ a < 2 ^ L`. -/
theorem cycle_profile_520 {n L : Nat} (hn : 0 < n) (hc : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) :
    520 ≤ L ∧ 0 < oddCount n L ∧ oddCount n L < L ∧ 3 ^ oddCount n L < 2 ^ L :=
  ⟨length_ge_520 hn hc hnr, oddCount_pos_of_accCycle hn hc,
   Cycle.oddCount_lt_length_of_accCycle hn hc.1 hc.2,
   Cycle.two_pow_gt_three_pow_of_accCycle hn hc.1 hc.2⟩

end CycleLength520
end Collatz
