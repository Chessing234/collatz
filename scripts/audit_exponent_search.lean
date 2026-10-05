import Collatz.Exploration.ExponentSearch

open Collatz.Exploration.ExponentSearch

#print axioms search_sound
#print axioms search_complete
#print axioms search_none_iff
#print axioms search_first
#print axioms findUnitExponent_success
#print axioms findUnitExponent_sound

example : search 9 7 6 0 = some 4 := by decide
example : search 9 7 4 0 = none := by decide
example : search 9 7 6 5 = some 10 := by decide
example : search 9 3 6 0 = none := by decide
example : findUnitExponent 0 0 = some 0 := by decide
example : findUnitExponent 1 2 = some 1 := by decide
example : findUnitExponent 2 7 = some 4 := by decide
example : findUnitExponent 3 11 = some 13 := by decide
example : findUnitExponent 4 7 = some 16 := by decide
example : findUnitExponent 3 3 = none := by decide
example : ∀ e, 0 ≤ e → e < 6 → (2:Nat)^e%9 ≠ 3%9 :=
  (search_none_iff 9 3 6 0).mp (by decide)
example : ∀ f, 5 ≤ f → f < 10 → (2:Nat)^f%9 ≠ 7%9 :=
  search_first (q := 9) (z := 7) (fuel := 6) (start := 5) (e := 10) (by decide)
