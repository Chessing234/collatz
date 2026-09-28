import Collatz.Strategy.PeriodicTwoDefectOdd

#print axioms Collatz.PeriodicTwoDefect.same_fibre
#print axioms Collatz.PeriodicTwoDefect.defect_locations
#print axioms Collatz.PeriodicTwoDefect.nine_necessary
#print axioms Collatz.PeriodicTwoDefect.label_rigidity
#print axioms Collatz.PeriodicTwoDefect.two_defects_iff_all
#print axioms Collatz.PeriodicTwoDefectOdd.doubling_invariant
#print axioms Collatz.PeriodicTwoDefectOdd.exact_positions
#print axioms Collatz.PeriodicTwoDefectOdd.two_defect_classification

#print axioms Collatz.PeriodicTwoDefectOdd.exists_two_iff_nine
#print axioms Collatz.PeriodicTwoDefectOdd.positions_of_two

open Collatz Collatz.PeriodicRigidity Collatz.PeriodicTwoDefectOdd

-- Independent kernel-evaluated concrete example, using the actual Collatz map.
example : PeriodicDefectMinimum.defectCount 9
    (fun n => decide (n%9=3 ∨ n%9=6)) = 2 := by decide

-- The classification excludes two-error labels at modulus fifteen.
example (f : Nat → Bool) (hp : HasPeriod f 15) :
    ¬ (∃ r s, r < 30 ∧ s < 30 ∧ r ≠ s ∧
      ∀ n, Defect f n ↔ n%30=r ∨ n%30=s) := by
  intro he
  have h := (two_defect_classification (h:=5) (by decide) (by decide) hp).mp he
  have impossible : ¬ (5:Nat)%3=0 := by decide
  exact impossible h.1
