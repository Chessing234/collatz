import Collatz.Strategy.HeavyWord
import Collatz.Strategy.ClassCap
import Collatz.Strategy.CycleCriterion
import Collatz.Strategy.GapOne

/-!
# The profile of a counterexample, as it now stands

Everything the development knows about a hypothetical counterexample, collected
into two statements so that the next round of work has a single object to attack
rather than a bibliography.

`neverDropper_profile` is the divergence side.  A never-dropper at the verified
range satisfies, simultaneously:

* it is at least `768000` — the only archimedean input in the development, and
  the only thing in it that is not uniform in the constant `d` of `3x+d`;
* its parity word is **heavy** for its whole first `2592` steps: `2 ^ j ≤ 3 ^ a`
  exactly, with no factor of two, so no window in that range contracts;
* consequently its odd-step count never falls behind `j · log₃ 2` there;
* and on any window that *does* contract, the whole residue class is capped:
  `m · (2 ^ j − 3 ^ a) ≤ C_j`.

`cycle_profile` is the cycle side.  A nontrivial cycle satisfies, simultaneously:

* length at least `2593`;
* its gap `2 ^ L − 3 ^ a` is odd, is at least `5`, and **divides** its
  accumulator exactly — indeed `n` *is* the quotient, so the cycle point is
  computed by the word rather than chosen;
* conversely any word whose gap divides its accumulator is a cycle, so nothing
  dynamical is left to check;
* the criterion is a property of the cycle and not of the point one starts at,
  since every divisor of the gap survives rotation;
* at most one cycle point of length `L` lies in each class modulo `2 ^ L`.

The two profiles share one shape: in both, the parity word determines everything
and the only remaining question is arithmetic — whether the word's gap can divide
the word's accumulator (cycles), or whether heaviness can persist for ever
(divergence).  Neither question has an answer here.  What the round established
is that no congruence, no valuation, no finite quotient and no `d`-uniform
argument can supply one, so the next mechanism must come from the arithmetic of
that divisibility itself — where the only working example so far is the order
obstruction of `OneRunOrder`.
-/

namespace Collatz
namespace Profile

open Reach Congruence AffineExact AccCycle

/-- **The divergence profile.**  Everything currently known about a
never-dropper, at once. -/
theorem neverDropper_profile {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    768000 ≤ m ∧
    (∀ j : Nat, j ≤ 2592 → 2 ^ j ≤ 3 ^ oddCount m j) ∧
    (∀ j : Nat, 3 ^ oddCount m j < 2 ^ j → m * (2 ^ j - 3 ^ oddCount m j) ≤ affineC j m) := by
  have hbig : 768000 ≤ m := CycleLength2593.ge_verified_768000 hn hnr hm
  have hmpos : 0 < m := by omega
  refine ⟨hbig, ?_, ?_⟩
  · intro j hj
    exact HeavyWord.heavy_window_2592 hmpos hbig hnd hj
  · intro j hgap
    exact ClassCap.cap_of_never_drops hmpos hnd hgap

/-- **The cycle profile.**  Everything currently known about a nontrivial
cycle, at once. -/
theorem cycle_profile {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) :
    2593 ≤ L ∧
    (2 ^ L - 3 ^ oddCount n L) % 2 = 1 ∧
    (2 ^ L - 3 ^ oddCount n L) * n = affineC L n ∧
    (2 ^ L - 3 ^ oddCount n L) ∣ affineC L n ∧
    n = affineC L n / (2 ^ L - 3 ^ oddCount n L) := by
  refine ⟨CycleLength2593.length_ge_2593 hn h hnr, CycleAccumulator.cycle_gap_odd hn h,
    CycleAccumulator.cycle_gap_mul hn h, CycleAccumulator.cycle_gap_dvd hn h,
    CycleAccumulator.cycle_eq_div hn h⟩

/-- The gap of a nontrivial cycle is at least five: one, two and three are each
excluded outright by `GapOne`. -/
theorem cycle_gap_ge_five {n L : Nat} (hn : 3 ≤ n) (h : AccIsCycleOf n L) :
    5 ≤ 2 ^ L - 3 ^ oddCount n L :=
  GapOne.gap_ge_five_of_nontrivial hn h

/-- **The criterion, in the form the next round should attack.**  For a positive
`x` whose window contracts, being a cycle point is *equivalent* to the gap
dividing the accumulator — an arithmetic condition on the parity word with no
orbit in it. -/
theorem cycle_iff_arithmetic {x L : Nat} (hx : 0 < x) (hL : 0 < L)
    (hgap : 3 ^ oddCount x L < 2 ^ L) :
    acceleratedOrbit L x = x ↔ (2 ^ L - 3 ^ oddCount x L) * x = affineC L x :=
  CycleCriterion.cycle_iff_gap_mul hx hL hgap

end Profile
end Collatz
