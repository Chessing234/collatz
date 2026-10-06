import Collatz.Exploration.PeriodQuotient
open Collatz.Exploration.PeriodQuotient

example : periodQuotient 0 = 1 := by decide
example : periodQuotient 1 = 1 := by decide
example : periodQuotient 2 = 7 := by decide
example : periodQuotient 3 = 9709 := by decide
example : 3^4*periodQuotient 4+1 = 2^54 := by decide
example : 0 < periodQuotient 100 := periodQuotient_positive 100
example : 1 < 3^100*periodQuotient 100+1 := period_factor_gt_one 100

#print axioms periodQuotient_exact
#print axioms periodQuotient_positive
#print axioms period_factor_gt_one
