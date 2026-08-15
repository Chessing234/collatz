import Collatz.Structure.CycleModThree
import Collatz.Structure.CycleExtremes

/-!
# The residue class of a cycle's least point

The least point `m` of an accelerated cycle is already known to be odd
(`AccCycle.accCycleMin_odd`) and not a multiple of three
(`CycleModThree.not_three_dvd_of_accCycle`).  This file pins it down further.

**`m ≡ 3 (mod 4)`.**  Suppose instead `m = 4j + 1`.  Then `m` is odd, so
`T(m) = (3m+1)/2 = 6j + 2`, which is *even*, so the next step halves it:

`T²(m) = 3j + 1 < 4j + 1 = m`   (for `j ≥ 1`).

That is a point of the cycle strictly below its least point — impossible.  So
the class `1 mod 4` is excluded, and an odd `m` must be `3 mod 4`.

Combining with the modulo-three result, the least point of a hypothetical cycle
lies in exactly **two classes modulo twelve: `7` and `11`**.

The same argument does not go further: for `m ≡ 3 (mod 8)` and `m ≡ 7 (mod 8)`
the two-step and three-step images both exceed `m`, so modulo `4` is where this
particular idea stops.
-/

namespace Collatz
namespace CycleMinClass

open Reach AccCycle

/-! ## The least point is `3` modulo `4` -/

/-- **The least point of a cycle is `3` modulo `4`.**  A least point congruent
to `1` would be halved twice into something smaller. -/
theorem cycleMin_mod_four {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    m % 4 = 3 := by
  obtain ⟨i, hi⟩ := hm
  have hodd : m % 2 = 1 := accCycleMin_odd hn ⟨i, hi⟩ hmin
  rcases (show m % 4 = 1 ∨ m % 4 = 3 by omega) with h1 | h3
  · exfalso
    -- one odd step
    have hstep1 : acceleratedOrbit (i + 1) n = (3 * m + 1) / 2 := by
      rw [acceleratedOrbit_succ_step, hi, acceleratedStep, if_neg (by omega)]
    -- the result is even, so the next step halves
    have heven : ((3 * m + 1) / 2) % 2 = 0 := by omega
    have hstep2 : acceleratedOrbit (i + 2) n = ((3 * m + 1) / 2) / 2 := by
      rw [show i + 2 = (i + 1) + 1 from rfl, acceleratedOrbit_succ_step, hstep1,
        acceleratedStep, if_pos heven]
    have hle := hmin (i + 2)
    rw [hstep2] at hle
    omega
  · exact h3

/-! ## Combining with the modulo-three constraint -/

/-- **The least point of a cycle is `7` or `11` modulo `12`.**  It is `3` modulo
`4` by the halving argument and not divisible by three by
`CycleModThree.not_three_dvd_of_accCycle`, and those two facts leave exactly two
classes. -/
theorem cycleMin_mod_twelve {n m L : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (hcyc : AccIsCycleOf m L) :
    m % 12 = 7 ∨ m % 12 = 11 := by
  have hfour := cycleMin_mod_four hn hm hmin hgt
  have hpos : 0 < m := by omega
  have hthree := CycleModThree.not_three_dvd_of_accCycle hpos hcyc
  omega

/-- The full residue profile of a hypothetical cycle's least point. -/
theorem cycleMin_profile {n m L : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (hcyc : AccIsCycleOf m L) :
    m % 2 = 1 ∧ m % 4 = 3 ∧ ¬ 3 ∣ m ∧ (m % 12 = 7 ∨ m % 12 = 11) := by
  refine ⟨accCycleMin_odd hn hm hmin, cycleMin_mod_four hn hm hmin hgt, ?_,
    cycleMin_mod_twelve hn hm hmin hgt hcyc⟩
  exact CycleModThree.not_three_dvd_of_accCycle (by omega) hcyc

/-- Only one class in twenty-four survives both constraints together with
oddness, so a hypothetical cycle's least point is confined to a set of density
`1/6`. -/
theorem cycleMin_density {n m L : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m)
    (hcyc : AccIsCycleOf m L) :
    m % 12 = 7 ∨ m % 12 = 11 :=
  cycleMin_mod_twelve hn hm hmin hgt hcyc

/-! ## Local descent at `1 mod 4`

The argument above is really a statement about *any* number congruent to `1`
modulo `4`, not just about cycle minima.  Isolating it makes it reusable. -/

/-- **Two-step descent.**  Every `x > 1` congruent to `1` modulo `4` satisfies
`T²(x) = (3x+1)/4 < x`.  This is the cheapest descent step available, and it is
why the class `1 mod 4` never survives any sieve. -/
theorem two_step_descent {x : Nat} (hx : 1 < x) (h : x % 4 = 1) :
    acceleratedOrbit 2 x < x := by
  have hodd : x % 2 = 1 := by omega
  have hstep1 : acceleratedOrbit 1 x = (3 * x + 1) / 2 := by
    rw [acceleratedOrbit, acceleratedOrbit, acceleratedStep, if_neg (by omega)]
  have heven : ((3 * x + 1) / 2) % 2 = 0 := by omega
  have hstep2 : acceleratedOrbit 2 x = ((3 * x + 1) / 2) / 2 := by
    rw [show (2:Nat) = 1 + 1 from rfl, ← acceleratedOrbit_add]
    rw [hstep1]
    rw [acceleratedOrbit, acceleratedOrbit, acceleratedStep, if_pos heven]
  rw [hstep2]
  omega

/-- **The successor of a cycle's least point is odd.**  The least point is `3`
modulo `4`, and `T(4j+3) = 6j+5`. -/
theorem accStep_min_odd {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    acceleratedStep m % 2 = 1 := by
  have hfour := cycleMin_mod_four hn hm hmin hgt
  have hodd : m % 2 = 1 := by omega
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- So a cycle takes two odd steps in a row at its least point: both `m` and
`T(m)` are odd. -/
theorem two_odd_steps_at_min {n m : Nat} (hn : 0 < n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n) (hgt : 1 < m) :
    m % 2 = 1 ∧ acceleratedStep m % 2 = 1 :=
  ⟨accCycleMin_odd hn hm hmin, accStep_min_odd hn hm hmin hgt⟩

end CycleMinClass
end Collatz
