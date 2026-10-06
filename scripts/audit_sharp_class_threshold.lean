import Collatz.Exploration.SharpClassThreshold
open Collatz Collatz.Exploration.SharpClassThreshold

example : exceptionLimit 3 4 1 1 = 0 := by decide
example : exceptionLimit 3 8 100 5 = 19 := by decide
example : 3*20+100 < 8*20+5 :=
  (drop_index_iff (by decide) (by decide)).mpr (by decide)
example : acceleratedOrbit 2 (2^2*1+1) < 2^2*1+1 :=
  (class_drop_index_iff (by decide) (by decide)).mpr (by decide)
example : acceleratedOrbit 3 (2^3*100+5) < 2^3*100+5 :=
  representative_drop_extends (by decide) (by decide) 100

#print axioms nondrop_index_iff
#print axioms all_indices_drop
#print axioms exceptionLimit_le_offset
#print axioms drop_index_iff
#print axioms class_drop_index_iff
#print axioms representative_drop_extends
#print axioms floor_sharp_bound
