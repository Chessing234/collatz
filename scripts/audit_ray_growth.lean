import Collatz.Exploration.RayGrowth
set_option maxRecDepth 10000
open Collatz Collatz.Exploration.RayGrowth
open Collatz.Exploration.AffineRay Collatz.Exploration.InverseClassRay

example : 2^10*3 ≤ ray 1 0 1 3 10 := binary_lower (by decide) 10
example : ray 1 0 1 3 10 = 3072 := by decide
example : 10 ≤ Nat.log2 3072 := index_below_cutoff (A := 1) (B := 0) (c := 1) (m := 3) (j := 10) (by decide) (by decide) (by decide)
example : 2^100 ≤ rayInput 3 7 18 100 := rayInput_binary_lower (by decide) 100
example : 1 ≤ Nat.log2 39768215 :=
  rayInput_index_bound (k := 3) (r := 7) (m := 18) (j := 1) (by decide) (by decide)
example : ray 0 0 0 0 100 = 0 := by decide

#print axioms geometric_lower
#print axioms binary_lower
#print axioms binary_lower_positive
#print axioms index_below_cutoff
#print axioms rayInput_binary_lower
#print axioms rayInput_index_bound
