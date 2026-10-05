import Collatz.Exploration.TraceCertificate

open Collatz Collatz.Exploration.TraceCertificate

set_option maxRecDepth 4000

#print axioms endpoint_sound
#print axioms preAbove_sound
#print axioms convergence_sound
#print axioms first_descent_sound
#print axioms accelerated_first_sound
#print axioms valid_append
#print axioms convergence_complete
#print axioms first_descent_complete

example : valid 3 [10,5,16,8,4,2] = true := by decide
example : firstDescentCheck 3 [10,5,16,8,4,2] = true := by decide
example : convergenceCheck 3 [10,5,16,8,4,2,1] = true := by decide
example : firstDescentCheck 3 [10,5,16,8,4,2,1] = false := by decide
example : valid 3 [10,6,3] = false := by decide
example : convergenceCheck 0 [] = false := by decide
example : convergenceCheck 1 [] = true := convergence_empty_one
example : Collatz.Exploration.OrbitFloor.Converges 3 :=
  convergence_sound (xs := [10,5,16,8,4,2,1]) (by decide)
example : Collatz.Exploration.FirstDescent.FirstStandard 3 6 :=
  first_descent_sound (xs := [10,5,16,8,4,2]) (by decide)
example : valid 3 ([10,5]++[16,8,4,2,1]) = true :=
  valid_append (xs := [10,5]) (ys := [16,8,4,2,1]) (by decide) (by decide)

-- Generated traces check every transition and every pre-drop state.
example : firstDescentCheck 27 (trace 27 96) = true := by decide
example : firstDescentCheck 27 (trace 27 95) = false := by decide
example : firstDescentCheck 27 (trace 27 97) = false := by decide
example : convergenceCheck 27 (trace 27 111) = true := by decide
example : ∀ n k, orbit k n = 1 → convergenceCheck n (trace n k) = true := by
  intro n k hk
  exact (convergence_complete k n).2 hk
