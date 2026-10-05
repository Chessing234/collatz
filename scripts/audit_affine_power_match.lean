import Collatz.Exploration.AffinePowerMatch

open Collatz.Exploration.AffinePowerMatch

#print axioms translate_of_residue
#print axioms large_matching_power
#print axioms power_match
#print axioms power_match_above
#print axioms no_power_match_of_nonunit

-- The translate specification includes modulus zero, where residue equality
-- forces exact equality; this edge case is not used by ternary matching.
example : ∃ m, 0*m+7 = 7 := translate_of_residue (by decide) (by decide)
example : ∃ m, 9*m+7 = 65536 := translate_of_residue (by decide) (by decide)
example : 9*7281+7 = (2:Nat)^16 := by decide
example : ∃ m e, 100 < m ∧ 9*m+7 = (2:Nat)^e :=
  power_match 2 7 100 (Or.inr (by decide))
example : ∃ m e, 100 < m ∧ 27*m+11 = (2:Nat)^e :=
  power_match 3 11 100 (Or.inr (by decide))
example : ∃ m e, 100 < m ∧ 1000000 < (2:Nat)^e ∧ m = (2:Nat)^e := by
  simpa using power_match_above 0 0 100 1000000 (Or.inl rfl)
example : ∀ m e, 9*m+3 ≠ (2:Nat)^e := by
  intro m e
  exact no_power_match_of_nonunit (by decide : 0 < 2) (by decide)
