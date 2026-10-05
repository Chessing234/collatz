import Collatz.Exploration.ExponentRaise

open Collatz.Exploration.ExponentRaise

#print axioms below_bitLength
#print axioms raise_ge
#print axioms raised_power_large
#print axioms raised_power_residue
#print axioms keep_sufficient
#print axioms raise_size_bound

example : bitLength 0 = 1 := by decide
example : bitLength 1 = 1 := by decide
example : bitLength 1023 = 10 := by decide
example : bitLength 1024 = 11 := by decide
example : raiseExponent 3 9 26 = 9 := by decide
example : raiseExponent 3 9 27026 = 27 := by decide
example : raiseExponent 2 1 9002 = 19 := by decide
example : (2:Nat)^27%27 = (2:Nat)^9%27 :=
  raised_power_residue 3 9 27026
example : 9002 < (2:Nat)^19 := raised_power_large 2 1 9002
example : raiseExponent 0 0 0 = 0 := by decide
example : raiseExponent 0 0 1000 = 11 := by decide
