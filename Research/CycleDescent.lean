import Collatz.Structure.Cycle

/-!
The user's cycle-descent argument, with its exact hypotheses.
These are elementary consequences of the existing cycle-minimum lemmas,
not a new proof of Collatz or a claim of mathematical novelty.

Check with: lake env lean Research/CycleDescent.lean
-/

namespace Collatz.CycleDescent
open Cycle Reach

/-- A member of a cycle eventually goes lower exactly when it is above
the cycle's minimum. -/
theorem drops_iff_above_minimum {n L : Nat} (hc : IsCycleOf n L) :
    (∃ k : Nat, orbit k n < n) ↔ cycleMin n L < n := by
  constructor
  · intro ⟨k, hk⟩
    exact Nat.lt_of_le_of_lt (cycleMin_le_orbit hc k) hk
  · intro hmin
    obtain ⟨k, _, hk⟩ := cycleMin_attained hc
    exact ⟨k, hk ▸ hmin⟩

/-- The descent from a nonminimum member happens strictly before a full
return to that member. This makes the cycle argument quantitative. -/
theorem drops_within_period_iff_above_minimum {n L : Nat} (hc : IsCycleOf n L) :
    (∃ k : Nat, 0 < k ∧ k < L ∧ orbit k n < n) ↔ cycleMin n L < n := by
  constructor
  · intro ⟨k, _, _, hk⟩
    exact Nat.lt_of_le_of_lt (cycleMin_le_orbit hc k) hk
  · intro hmin
    obtain ⟨k, hkL, hk⟩ := cycleMin_attained hc
    have hdrop : orbit k n < n := hk ▸ hmin
    have hkpos : 0 < k := by
      cases k with
      | zero => simp [orbit] at hdrop
      | succ k => omega
    exact ⟨k, hkpos, hkL, hdrop⟩

/-- The minimum itself never goes lower, regardless of how many times
we go around the cycle. -/
theorem minimum_never_drops {n L : Nat} (hc : IsCycleOf n L) :
    ¬ ∃ k : Nat, orbit k (cycleMin n L) < cycleMin n L := by
  intro ⟨k, hk⟩
  exact Nat.not_lt_of_ge (cycleMin_le_own_orbit hc k) hk

/-- Requiring descent at EVERY cycle member greater than 1 is precisely
the assertion that all positive cycles are the familiar trivial cycle.
This theorem does not prove either side unconditionally. -/
theorem periodic_descent_iff_only_trivial_cycles :
    (∀ n : Nat, 1 < n → Periodic n → ∃ k : Nat, orbit k n < n) ↔
    (∀ n : Nat, 0 < n → Periodic n → InTrivialCycle n) := by
  constructor
  · intro hdrop n hn hper
    obtain ⟨L, hc⟩ := hper
    have hmpos := cycleMin_pos hn hc
    have hmone : cycleMin n L = 1 := by
      by_cases hle : cycleMin n L ≤ 1
      · omega
      · have hgt : 1 < cycleMin n L := by omega
        have hmper : Periodic (cycleMin n L) := ⟨L, isCycleOf_cycleMin hc⟩
        exact False.elim (minimum_never_drops hc (hdrop _ hgt hmper))
    obtain ⟨k, _, hk⟩ := cycleMin_attained hc
    have hreach : ReachesOne n := ⟨k, hk.symm.trans hmone⟩
    exact mem_trivial_of_periodic_of_reachesOne ⟨L, hc⟩ hreach
  · intro htrivial n hn hper
    obtain ⟨k, hk⟩ := reachesOne_of_inTrivialCycle (htrivial n (by omega) hper)
    exact ⟨k, by rw [hk]; exact hn⟩

/-- Two explicit missing hypotheses would complete the argument:
every positive orbit enters a cycle, and every cycle member above 1 drops.
Neither hypothesis is asserted here. -/
theorem collatz_of_eventual_cycle_and_periodic_descent
    (henter : ∀ n : Nat, 0 < n → ∃ k : Nat, Periodic (orbit k n))
    (hdrop : ∀ n : Nat, 1 < n → Periodic n → ∃ k : Nat, orbit k n < n) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨k, hk⟩ := henter n hn
  have htrivial := periodic_descent_iff_only_trivial_cycles.mp hdrop
    (orbit k n) (orbit_positive hn k) hk
  exact reaches_of_orbit_reaches (reachesOne_of_inTrivialCycle htrivial)

/-- The proposed induction works if descent is established for EVERY
starting value greater than 1, with no assumption that it lies on a cycle.
The hypothesis `hdrop` is the unproved part of this route to Collatz. -/
theorem collatz_of_universal_descent
    (hdrop : ∀ n : Nat, 1 < n → ∃ k : Nat, orbit k n < n) :
    CollatzConjecture := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hone : n = 1
    · subst n
      exact reachesOne_one
    · obtain ⟨k, hk⟩ := hdrop n (by omega)
      have hsmaller : ReachesOne (orbit k n) :=
        ih (orbit k n) hk (orbit_positive hn k)
      exact reaches_of_orbit_reaches hsmaller

end Collatz.CycleDescent

#print axioms Collatz.CycleDescent.drops_iff_above_minimum
#print axioms Collatz.CycleDescent.drops_within_period_iff_above_minimum
#print axioms Collatz.CycleDescent.minimum_never_drops
#print axioms Collatz.CycleDescent.periodic_descent_iff_only_trivial_cycles
#print axioms Collatz.CycleDescent.collatz_of_eventual_cycle_and_periodic_descent
#print axioms Collatz.CycleDescent.collatz_of_universal_descent
