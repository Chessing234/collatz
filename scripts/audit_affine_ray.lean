import Collatz.Exploration.AffineRay
open Collatz.Exploration.AffineRay

-- The 151 example has A=27, B=26, m=18, and period power 2^18.
example : 27*9709+1 = 2^18 := by decide
example : 27*18+26 = 2^9 := by decide
example : ray 27 26 9709 18 1 = 4971026 := by decide
example : 27*ray 27 26 9709 18 2+26 = 2^(18*2+9) :=
  power_ray (by decide) (by decide) 2
example : ray 27 26 9709 18 1 < ray 27 26 9709 18 2 :=
  ray_strict_step (by decide) (by decide) 1
example : ray 0 0 0 0 10 = 0 := by decide
example : ray 1 0 1 3 5 = 96 := by decide

#print axioms endpoint_transport
#print axioms endpoint_ray
#print axioms power_ray
#print axioms ray_positive
#print axioms ray_strict_step
