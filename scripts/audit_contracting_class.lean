import Collatz.Exploration.ContractingClass
open Collatz Collatz.Exploration.ContractingClass

example : 3*(2:Nat)+1 < 4*2+1 := affine_drop (by decide) (by decide)
example : acceleratedOrbit 2 (2^2*2+1) < 2^2*2+1 :=
  class_drop (by decide) (by decide)
example : (2^2*0+1 ≤ acceleratedOrbit 2 (2^2*0+1)) ↔
    (2^2-3^(oddCount 1 2))*0+1 ≤ acceleratedOrbit 2 1 :=
  class_nondrop_iff (by decide)
example : ¬ (2^3*0+5 ≤ acceleratedOrbit 3 (2^3*0+5)) := by decide
example : (2^2-3^(oddCount 1 2))*1+1 > acceleratedOrbit 2 1 := by decide
example : 3^(oddCount 3 2) > 2^2 := by decide
example : ∃ t, 2 ≤ t ∧ t ≤ 2*2 ∧ orbit t (2^2*2+1) < 2^2*2+1 :=
  class_standard_drop (by decide) (by decide)

#print axioms affine_nondrop_iff
#print axioms affine_exception_bound
#print axioms affine_drop
#print axioms class_nondrop_iff
#print axioms class_drop
#print axioms class_standard_drop
#print axioms floor_index_bound
#print axioms collatz_of_contracting_floor_cover
