import Collatz.Exploration.ThreePowerLift

open Collatz.Exploration.ThreePowerLift

#print axioms cube_lift
#print axioms cubeCoefficient_mod_three
#print axioms exact_lift
#print axioms period_mod
#print axioms not_period_next

example : cubeCoefficient 1 1 = 7 := by decide
example : cubeCoefficient 3 7 = 9709 := by decide
example : (2:Nat)^2 = 3^1*1+1 := by decide
example : (2:Nat)^6 = 3^2*7+1 := by decide
example : (2:Nat)^18 = 3^3*9709+1 := by decide
example : (2:Nat)^2%3 = 1 := period_mod 0
example : (2:Nat)^6%9 = 1 := period_mod 1
example : (2:Nat)^18%27 = 1 := period_mod 2
example : (2:Nat)^2%9 ≠ 1 := not_period_next 0
example : (2:Nat)^6%27 ≠ 1 := not_period_next 1
example : (2:Nat)^18%81 ≠ 1 := not_period_next 2
