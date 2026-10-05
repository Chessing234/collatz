import Collatz.Strategy.PrimePowerBoundary

#print axioms Collatz.PrimePowerBoundary.power_divides_one_of_three
#print axioms Collatz.PrimePowerBoundary.obstruction_cardinality
#print axioms Collatz.PrimePowerBoundary.two_boundary_cardinality
#print axioms Collatz.PrimePowerBoundary.zero_boundary_impossible
#print axioms Collatz.PrimePowerBoundary.four_le_boundary
#print axioms Collatz.PrimePowerBoundary.pair_boundary_sharp
#print axioms Collatz.PrimePowerBoundary.prime_power_sharp

open Collatz.BoundaryCuts
-- A square modulus, with the actual branch maps.
example : boundary ([1,2] : List (Fin 121)) (fun z => 2*z) +
    boundary ([1,2] : List (Fin 121)) (oddBranch 61)=4 := by decide

-- The algebraic argument cannot extend unchanged to arbitrary composites.
-- This is an annihilator root, NOT a realized graph cut.
example : (105 : Fin 143)*12*((12 : Fin 143)^2-1)=0 := by decide
example : (12 : Fin 143) ≠ 0 ∧ (12 : Fin 143) ≠ 1 ∧
    (12 : Fin 143) ≠ -1 := by decide
