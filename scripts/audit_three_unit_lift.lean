import Collatz.Exploration.ThreeUnitLift

open Collatz.Exploration.ThreeUnitLift

#print axioms digit_cover
#print axioms power_correction
#print axioms correction_mod_three
#print axioms lifted_congruence
#print axioms three_lifts

example : (1+3*1)^0%9 = 1 := by decide
example : (1+3*1)^1%9 = 4 := by decide
example : (1+3*1)^2%9 = 7 := by decide
example : (2*(1+3*1)^0)%9 = 2 := by decide
example : (2*(1+3*1)^1)%9 = 8 := by decide
example : (2*(1+3*1)^2)%9 = 5 := by decide
example : ∃ t, t ≤ 2 ∧ (2*(1+9*7)^t)%27 = 11%27 :=
  three_lifts 2 11 9 7 (by decide) (by decide) (by decide) (by decide)
example : correction 2 9 7 0 = 0 := by decide
example : correction 2 9 7 1 = 14 := by decide
example : correction 2 9 7 2 = 910 := by decide
