import Collatz.Strategy.CycleDescentBridge
#print axioms Collatz.CycleDescentBridge.returns_to_base
#print axioms Collatz.CycleDescentBridge.higher_cycle_member_descends
#print axioms Collatz.CycleDescentBridge.cycle_minimum_never_descends
#print axioms Collatz.CycleDescentBridge.collatz_of_universal_descent
#print axioms Collatz.CycleDescentBridge.universal_descent_iff_collatz
#print axioms Collatz.CycleDescentBridge.cycle_minimum_eq_one_of_descent
-- A concrete instance: start at 4 in the cycle 1 -> 4 -> 2 -> 1.
example : ∃ j, 0 < j ∧ Collatz.orbit j 4 < 4 := by
  have h := Collatz.CycleDescentBridge.higher_cycle_member_descends
    (m := 1) (L := 3) (i := 1) (by decide) (by decide) (by decide)
  exact h
