import Collatz.Strategy.Profile
import Collatz.Strategy.Frontier8917

/-!
# The counterexample profile, at the extended range

`Strategy.Profile` collects everything known about a hypothetical counterexample
into two statements, "so that the next round of work has a single object to
attack rather than a bibliography".  Three of its constants have since moved:

| clause | `Profile` | here |
|---|---|---|
| a never-dropper is at least | `768 000` | `1 664 599` |
| its word is heavy for its first | `2592` steps | `5625` steps |
| a nontrivial cycle has length at least | `2593` | `8917` |

Nothing else changes, and no clause is new.  The structural content is exactly
`Profile`'s: in both halves the parity word determines everything, and the
remaining question is arithmetic — whether the word's gap can divide the word's
accumulator (cycles), or whether heaviness can persist for ever (divergence).
Neither question has an answer here either.

The improvement is entirely the verified range, `1 086 464 → 1 665 024`, spent
through the certificate ladder.  Round XLIV's result that the range required per
riser diverges applies unchanged, so this is a wider window on the same object,
not a step toward closing it.
-/

namespace Collatz
namespace ProfileSharp

open Reach AccCycle AffineExact

/-- **The divergence profile, sharpened.**  `Profile.neverDropper_profile` with
the range and window of the extended sweep. -/
theorem neverDropper_profile_sharp {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    1664599 ≤ m ∧
    (∀ j : Nat, j ≤ 5625 → 2 ^ j ≤ 3 ^ oddCount m j) ∧
    (∀ j : Nat, 3 ^ oddCount m j < 2 ^ j → m * (2 ^ j - 3 ^ oddCount m j) ≤ affineC j m) := by
  have hbig : 1664599 ≤ m := Frontier8917.ge_verified_1664599 hn hnr hm
  refine ⟨hbig, ?_, ?_⟩
  · intro j hj
    exact Frontier8917.heavy_window_5625 hn hnr hm hnd hj
  · intro j hgap
    exact ClassCap.cap_of_never_drops (by omega) hnd hgap

/-- **The cycle profile, sharpened.**  `Profile.cycle_profile` at the frontier
this development now reaches. -/
theorem cycle_profile_sharp {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) :
    8917 ≤ L ∧
    (2 ^ L - 3 ^ oddCount n L) % 2 = 1 ∧
    (2 ^ L - 3 ^ oddCount n L) * n = affineC L n ∧
    (2 ^ L - 3 ^ oddCount n L) ∣ affineC L n ∧
    n = affineC L n / (2 ^ L - 3 ^ oddCount n L) :=
  ⟨Frontier8917.length_ge_8917 hn h hnr, CycleAccumulator.cycle_gap_odd hn h,
    CycleAccumulator.cycle_gap_mul hn h, CycleAccumulator.cycle_gap_dvd hn h,
    CycleAccumulator.cycle_eq_div hn h⟩

/-- The odd-step count of a never-dropper's first `5625` steps, as a single
number: more than `3541` of them. -/
theorem neverDropper_odd_steps {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    3541 < oddCount m 5625 :=
  Frontier8917.odd_steps_5625 hn hnr hm hnd

end ProfileSharp
end Collatz
