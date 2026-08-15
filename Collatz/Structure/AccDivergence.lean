import Collatz.Structure.AccCycle
import Collatz.Core.Pigeonhole

/-!
# The dichotomy for the accelerated map

`Collatz.Structure.Divergence` proves that a bounded orbit of the standard map
must enter a cycle.  The cycle-length bound of `Collatz.Structure.CycleLength`
is stated for the *accelerated* map, so the same dichotomy is needed there, and
this file supplies it.

The argument is unchanged: pigeonhole on a bounded orbit produces a repeat, and
a repeat past index `i` is a cycle through `T^i(n)`.
-/

namespace Collatz
namespace AccDivergence

open Reach AccCycle

/-- The accelerated orbit of `n` is bounded. -/
def AccBounded (n : Nat) : Prop := ∃ B : Nat, ∀ i : Nat, acceleratedOrbit i n ≤ B

/-- The accelerated orbit of `n` is unbounded. -/
def AccDivergent (n : Nat) : Prop := ∀ B : Nat, ∃ i : Nat, B < acceleratedOrbit i n

/-- Divergence is exactly failure of boundedness. -/
theorem accDivergent_iff_not_accBounded (n : Nat) : AccDivergent n ↔ ¬ AccBounded n := by
  constructor
  · intro hdiv hbdd
    obtain ⟨B, hB⟩ := hbdd
    obtain ⟨i, hi⟩ := hdiv B
    have := hB i
    omega
  · intro hnb B
    by_cases h : ∃ i, B < acceleratedOrbit i n
    · exact h
    · exact absurd ⟨B, fun i => by
        have : ¬ (B < acceleratedOrbit i n) := fun hc => h ⟨i, hc⟩
        omega⟩ hnb

/-- Failure of divergence is boundedness. -/
theorem accBounded_of_not_accDivergent {n : Nat} (h : ¬ AccDivergent n) : AccBounded n := by
  by_cases hb : AccBounded n
  · exact hb
  · exact absurd ((accDivergent_iff_not_accBounded n).mpr hb) h

/-- **The dichotomy.**  A bounded accelerated orbit enters a cycle. -/
theorem exists_accCycle_of_accBounded {n : Nat} (h : AccBounded n) :
    ∃ i L : Nat, AccIsCycleOf (acceleratedOrbit i n) L := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨i, j, hij, hfij⟩ :=
    Pigeonhole.exists_repeat_of_le (f := fun k => acceleratedOrbit k n) (B := B) hB
  refine ⟨i, j - i, by omega, ?_⟩
  have hsum : j - i + i = j := by omega
  calc acceleratedOrbit (j - i) (acceleratedOrbit i n)
      = acceleratedOrbit (j - i + i) n := acceleratedOrbit_add _ _ _
    _ = acceleratedOrbit j n := by rw [hsum]
    _ = acceleratedOrbit i n := hfij.symm

end AccDivergence
end Collatz
