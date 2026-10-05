import Collatz.Exploration.HalvingBlocks
set_option maxRecDepth 10000
open Collatz Collatz.Exploration.HalvingBlocks

example : orbit 10 (2^10*27) = 27 := by decide
example : acceleratedOrbit 10 (2^10*27) = 27 := by decide
example : orbit 0 (2^0*0) = 0 := by decide
example : orbit 16 (2^16) = 1 := by decide
example : acceleratedOrbit 3 151 = 2^9 := by decide
example : orbit (9+Collatz.Exploration.TimeChange.clock 151 3) 151 = 1 :=
  endpoint_hits (by decide)
example : orbit (111+7) (2^7*27) = 1 :=
  scale_successful_time (by decide) 7

#print axioms orbit_halving
#print axioms accelerated_halving
#print axioms endpoint_hits
#print axioms endpoint_time_bound
#print axioms scale_successful_time
