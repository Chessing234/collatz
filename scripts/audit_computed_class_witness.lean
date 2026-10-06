import Collatz.Exploration.ComputedClassWitness

open Collatz Collatz.Exploration.ComputedClassWitness Collatz.Exploration.OrbitFloor

#print axioms matchingIndex_spec
#print axioms converges_of_match
#print axioms classWitness_sound
#print axioms classWitness_success
#print axioms classWitness_total
#print axioms chosen_exponent_bound

example : classWitness 0 0 0 = some 1 := by decide
example : classWitness 1 0 1000 = some 4096 := by decide
example : classWitness 1 1 0 = some 21 := by decide
example : classWitness 3 7 0 = some 151 := by decide
example : classWitness 3 7 1000 = some 39768215 := by decide
example : classWitness 4 3 1000 = some 932067 := by decide
example : 0 < 151 ∧ 151%8 = 7 ∧ Converges 151 :=
  classWitness_sound (k := 3) (r := 7) (N := 0) (by decide)
example : 1000 < 932067 ∧ 932067%16 = 3 ∧ Converges 932067 :=
  classWitness_sound (k := 4) (r := 3) (N := 1000) (by decide)
example : ∀ r : Fin 8, (classWitness 3 r.val 1000).isSome = true := by decide
example : ∀ r : Fin 16, (classWitness 4 r.val 1000).isSome = true := by decide
