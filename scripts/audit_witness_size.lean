import Collatz.Exploration.WitnessSize
open Collatz Collatz.Exploration.WitnessSize
open Collatz.Exploration.ExponentRaise
open Collatz.Exploration.ExponentSearch

example : 2^(bitLength 0) ≤ 2*(0+1) := binary_power_bound 0
example : 2^(bitLength 1023) = 1024 := by decide
example : 2^(bitLength 1024) = 2048 := by decide
example : 151 ≤ 2^3*(2^(2*periodLength (oddCount 7 3))*
    (2*(3^(oddCount 7 3)*0+acceleratedOrbit 3 7+1)))+7 :=
  returned_size_bound (by decide)
example : 932067 ≤ 2^4*(2^(2*periodLength (oddCount 3 4))*
    (2*(3^(oddCount 3 4)*1000+acceleratedOrbit 4 3+1)))+3 :=
  returned_size_bound (by decide)

#print axioms binary_power_bound
#print axioms matchingIndex_le_power
#print axioms raised_value_bound
#print axioms constructed_size_bound
#print axioms returned_size_bound
