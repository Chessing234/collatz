import Collatz.Exploration.TimeChange

open Collatz Collatz.Exploration.TimeChange

#print axioms orbit_at_clock
#print axioms clock_cover
#print axioms lower_bounds_iff
#print axioms floor_iff
#print axioms accelerated_drop_of_standard
#print axioms standard_drop_of_accelerated
#print axioms bounded_iff

-- These examples catch the factor-of-two convention error: the clock is
-- variable, not simply twice the accelerated index.
example : clock 3 0 = 0 := by decide
example : clock 3 1 = 2 := by decide
example : clock 3 2 = 4 := by decide
example : clock 3 3 = 5 := by decide
example : clock 3 4 = 6 := by decide
example : clock 3 5 = 7 := by decide
example : orbit 7 3 = acceleratedOrbit 5 3 := by decide
example : clock 0 20 = 20 := by decide
example : orbit (clock 0 20) 0 = 0 := by decide
example : clock 1 2 = 3 := by decide
example : clock 27 59 = 96 := by decide

-- One witness is explicitly an omitted expansion. Its retained predecessor
-- must also be below the original input whenever the expansion is below it.
example : orbit (clock 3 1+1) 3 = 16 := by decide
example : ∀ n j, j ≤ clock n j ∧ clock n j ≤ 2*j := clock_bounds
