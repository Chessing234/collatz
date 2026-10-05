import Collatz.Exploration.ClassWitnessCost
set_option maxRecDepth 10000
open Collatz Collatz.Exploration.ClassWitnessCost
open Collatz.Exploration.ComputedClassWitness
open Collatz.Exploration.ExponentSearch

example : findUnitExponent 3 26 = some 9 := by decide
example : witnessTime 3 7 0 9 = 15 := by decide
example : orbit (witnessTime 3 7 0 9) 151 = 1 := by decide
example : witnessTime 4 3 1000 1 = 25 := by decide
example : findUnitExponent (oddCount 3 4) (acceleratedOrbit 4 3) = some 1 := by decide
example : orbit (witnessTime 4 3 1000 1) 932067 = 1 := by decide
example : ∃ t, orbit t 151 = 1 ∧
    t < 2*3+Collatz.Exploration.ExponentRaise.bitLength
      (3^(oddCount 7 3)*0+acceleratedOrbit 3 7)+
      2*periodLength (oddCount 7 3) := returned_time_bound (by decide)

#print axioms witnessTime_hits
#print axioms witnessTime_bound
#print axioms returned_time_bound
#print axioms quantitative_class_member
