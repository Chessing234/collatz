import Collatz.Exploration.RayEnumeration
set_option maxRecDepth 10000
open Collatz Collatz.Exploration.RayEnumeration
open Collatz.Exploration.InverseClassRay

example : inputsBelow 3 7 18 0 = [] := by decide
example : inputsBelow 3 7 18 150 = [] := by decide
example : inputsBelow 3 7 18 151 = [151] := by decide
example : inputsBelow 3 7 18 1000 = [151] := by decide
example : indicesBelow 0 0 1 16 = [0,1,2,3,4] := by decide
example : inputsBelow 0 0 1 16 = [1,2,4,8,16] := by decide
example : (inputsBelow 3 7 18 1000).length ≤ Nat.log2 1000+1 :=
  input_count_bound 3 7 18 1000
example : Collatz.Exploration.OrbitFloor.Converges 151 :=
  listed_converges (k := 3) (r := 7) (m := 18) (e := 9) (X := 1000)
    (by decide) (by decide)

#print axioms index_sound
#print axioms index_complete
#print axioms input_sound
#print axioms input_complete
#print axioms index_count_bound
#print axioms input_count_bound
#print axioms listed_converges
