import Collatz.Exploration.ThreePowerUnits

open Collatz.Exploration.ThreePowerUnits

#print axioms coverage_lift
#print axioms coverage_positive
#print axioms power_representation
#print axioms power_two_unit
#print axioms bounded_exponent
#print axioms power_period_shift
#print axioms unbounded_exponents
#print axioms unbounded_values

example : UnitCoverage 27 := coverage_positive 2
example : ∃ e, (2:Nat)^e%81 = 7%81 := power_representation 4 7 (by decide)
example : ∃ e, 100 ≤ e ∧ (2:Nat)^e%27 = 11%27 :=
  unbounded_exponents 3 11 100 (by decide)
example : ∃ e, 1000000 < (2:Nat)^e ∧ (2:Nat)^e%243 = 17%243 :=
  unbounded_values 5 17 1000000 (by decide)
example : (2:Nat)^16%81 = 7 := by decide
example : (2:Nat)^55%81 = 2 := by decide
example : (2:Nat)^8%27 = 13 := by decide
example : (2:Nat)^26%27 = 13 := by decide
example : (2:Nat)^(8+18*100)%27 = (2:Nat)^8%27 :=
  power_period_shift 27 18 8 100 (by decide) (by decide)

example : ∃ e, e < 54 ∧ (2:Nat)^e%81 = 7%81 :=
  bounded_exponent 3 7 (by decide)
example : ∀ z : Fin 27, z.val%3 ≠ 0 →
    ∃ e : Fin 18, (2:Nat)^e.val%27 = z.val := by decide
