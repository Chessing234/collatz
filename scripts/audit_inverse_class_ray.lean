import Collatz.Exploration.InverseClassRay
set_option maxRecDepth 10000
open Collatz Collatz.Exploration.InverseClassRay

example : rayInput 3 7 18 0 = 151 := by decide
example : rayInput 3 7 18 1 = 39768215 := by decide
example : acceleratedOrbit 3 (rayInput 3 7 18 2) = 2^45 :=
  rayInput_endpoint (k := 3) (r := 7) (m := 18) (e := 9) (by decide) 2
example : Collatz.Exploration.OrbitFloor.Converges (rayInput 3 7 18 100) :=
  rayInput_converges (e := 9) (by decide) 100
example : rayInput 3 7 18 100 < rayInput 3 7 18 101 :=
  rayInput_strict_step (by decide) 100
example : rayInput 4 3 29127 3%16 = 3 := rayInput_residue 4 3 29127 3
example : orbit 33 (rayInput 3 7 18 1) = 1 := by decide

#print axioms rayInput_residue
#print axioms rayInput_endpoint
#print axioms rayInput_hits
#print axioms rayInput_converges
#print axioms rayInput_strict_step
#print axioms rayInput_time_bound
