import Collatz.Structure.OddRuns
import Collatz.Structure.CycleExtremes
import Collatz.Structure.CycleMinClass

/-!
# What runs of odd steps cost

`OddRuns.climb_bounded` says a run of `j` consecutive odd steps from `x` forces
`2 ^ j ≤ x + 1`.  Climbing is rationed: to rise `j` times in a row you must
already be exponentially large in `j`.

That turns into constraints wherever the orbit is confined.

* On a **cycle**, every point is at most the greatest point `M`, so no run
  anywhere on the cycle exceeds `log₂(M + 1)`.  A cycle cannot contain a long
  climb unless it is correspondingly tall.
* At the **orbit minimum** `m` of a counterexample, runs are capped by `m`
  itself.

The file also re-derives `m ≡ 3 (mod 4)` from the run characterisation instead
of from the halving argument.  Two independent routes to the same congruence is
a useful consistency check on the whole development: `CycleMinClass` gets it by
exhibiting a descent, `OddRuns` by counting consecutive odd steps.
-/

namespace Collatz
namespace RunBounds

open Reach Congruence AccCycle CycleExtremes OddRuns

/-! ## Runs on a cycle -/

/-- **A cycle cannot contain a long climb.**  Any run of `j` consecutive odd
steps starting at a cycle point forces `2 ^ j ≤ M + 1`, where `M` is the cycle's
greatest point. -/
theorem oddRun_le_cycleMax {n L x j : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    {i : Nat} (hx : acceleratedOrbit i n = x) (hrun : OddRun x j) :
    2 ^ j ≤ cycleMax n L + 1 := by
  have hpos : 0 < x := by
    rw [← hx]; exact acceleratedOrbit_positive hn i
  have hclimb := climb_bounded hpos hrun
  have hle : x ≤ cycleMax n L := by
    rw [← hx]; exact le_cycleMax h i
  omega

/-- Restated as a bound on run length: a cycle of greatest point `M` admits no
run longer than `log₂(M + 1)`. -/
theorem no_long_run_of_cycle {n L x j : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    {i : Nat} (hx : acceleratedOrbit i n = x) (hrun : OddRun x j)
    (hbig : cycleMax n L + 1 < 2 ^ j) : False := by
  have := oddRun_le_cycleMax hn h hx hrun
  omega

/-! ## Runs at the orbit minimum -/

/-- A run at the orbit minimum is capped by the minimum itself. -/
theorem oddRun_le_min {n m j : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) (hrun : OddRun m j) :
    2 ^ j ≤ m + 1 := by
  have hpos : 0 < m := accCycleMin_pos hn hm
  exact climb_bounded hpos hrun

/-- **The orbit minimum starts with a run of length two**: it is odd, and so is
its successor. -/
theorem min_oddRun_two {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    OddRun m 2 := by
  intro i hi
  have hodd0 : m % 2 = 1 := accCycleMin_odd hn hm hmin
  have hodd1 : acceleratedStep m % 2 = 1 :=
    CycleMinClass.accStep_min_odd hn hm hmin hgt
  cases i with
  | zero =>
    rw [acceleratedOrbit]
    exact hodd0
  | succ i' =>
    have hi0 : i' = 0 := by omega
    subst hi0
    rw [acceleratedOrbit, acceleratedOrbit]
    exact hodd1

/-- **The congruence `m ≡ 3 (mod 4)`, re-derived.**  A run of length two is
exactly `−1` modulo `4`.  This is the same conclusion as
`CycleMinClass.cycleMin_mod_four`, reached by counting odd steps rather than by
exhibiting a descent. -/
theorem min_mod_four_via_runs {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    m % 4 = 3 := by
  have hrun := min_oddRun_two hn hm hmin hgt
  have hdvd : 2 ^ 2 ∣ (m + 1) := (oddRun_iff 2 m).mp hrun
  have h4 : (2:Nat) ^ 2 = 4 := by decide
  rw [h4] at hdvd
  omega

/-- The two derivations agree, which is a consistency check on the
development. -/
theorem mod_four_agrees {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    CycleMinClass.cycleMin_mod_four hn hm hmin hgt = min_mod_four_via_runs hn hm hmin hgt :=
  rfl

/-! ## A run of length three -/

/-- A third consecutive odd step at the minimum would force `m ≡ 7 (mod 8)`. -/
theorem min_mod_eight_of_run_three {m : Nat}
    (hrun : OddRun m 3) : m % 8 = 7 := by
  have hdvd : 2 ^ 3 ∣ (m + 1) := (oddRun_iff 3 m).mp hrun
  have h8 : (2:Nat) ^ 3 = 8 := by decide
  rw [h8] at hdvd
  omega

/-- Conversely `m ≡ 7 (mod 8)` gives three consecutive odd steps, so the sieve's
two surviving classes modulo `8` split exactly by run length: `3 mod 8` has a run
of two, `7 mod 8` a run of at least three. -/
theorem run_three_of_mod_eight {m : Nat} (h : m % 8 = 7) : OddRun m 3 := by
  refine (oddRun_iff 3 m).mpr ?_
  have h8 : (2:Nat) ^ 3 = 8 := by decide
  rw [h8]
  omega

/-- The classification of the two surviving classes modulo `8` by run length. -/
theorem mod_eight_run_dichotomy {m : Nat} (h3 : m % 4 = 3) :
    (m % 8 = 3 ∧ ¬ OddRun m 3) ∨ (m % 8 = 7 ∧ OddRun m 3) := by
  rcases (show m % 8 = 3 ∨ m % 8 = 7 by omega) with h | h
  · refine Or.inl ⟨h, fun hrun => ?_⟩
    have := min_mod_eight_of_run_three hrun
    omega
  · exact Or.inr ⟨h, run_three_of_mod_eight h⟩

end RunBounds
end Collatz
