import Collatz.Strategy.PeriodicTwoDefectAll

set_option maxRecDepth 4096

#print axioms Collatz.PeriodicTwoDefectAll.pair_bound
#print axioms Collatz.PeriodicTwoDefectAll.high_indegree_no_split
#print axioms Collatz.PeriodicTwoDefectAll.incoming_split_forces_period
#print axioms Collatz.PeriodicTwoDefectAll.half_period_one
#print axioms Collatz.PeriodicTwoDefectAll.pullback_two
#print axioms Collatz.PeriodicTwoDefectAll.descent_dichotomy
#print axioms Collatz.PeriodicTwoDefectAll.two_defect_shapes
#print axioms Collatz.PeriodicTwoDefectAll.half_shape_positions
#print axioms Collatz.PeriodicTwoDefectAll.third_shape_positions
#print axioms Collatz.PeriodicTwoDefectAll.two_defect_classification
#print axioms Collatz.PeriodicTwoDefectAll.exists_two_iff
#print axioms Collatz.PeriodicTwoDefectAll.third_shape_least_period
#print axioms Collatz.PeriodicTwoDefectAll.least_period_classification
#print axioms Collatz.PeriodicTwoDefectAll.count_eq_two_iff
#print axioms Collatz.PeriodicTwoDefectAll.counted_classification
#print axioms Collatz.PeriodicTwoDefectAll.two_defects_constant_off_three
#print axioms Collatz.PeriodicTwoDefectAll.three_le_of_separates_off_three
#print axioms Collatz.PeriodicTwoDefectAll.oneLabel_positions
#print axioms Collatz.PeriodicTwoDefectAll.oneLabel_count
#print axioms Collatz.PeriodicTwoDefectAll.sharp_core_minimum

open Collatz PeriodicRigidity PeriodicDefectMinimum PeriodicTwoDefectAll

-- Independently evaluate the original Collatz map and the actual defect count.
example : defectCount 6 (fun n => decide (n%6=0 ∨ n%6=3))=2 := by decide
example : defectCount 9 (fun n => decide (n%9=3 ∨ n%9=6))=2 := by decide
example : defectCount 18 (fun n => decide (n%18=0 ∨ n%18=9))=2 := by decide
example : defectCount 18 (fun n => decide (n%18=6 ∨ n%18=12))=2 := by decide
example : defectCount 72 (fun n => decide (n%72=24 ∨ n%72=48))=2 := by decide
example : defectCount 6 (fun n => decide (n%6=2 ∨ n%6=4))=5 := by decide
example : defectCount 36 (oneLabel 36)=3 := by decide

-- Infinite assertions instantiated at excluded and even moduli.
example : ¬∃ f : Nat → Bool, HasPeriod f 15 ∧ ExactlyTwo 15 f := by
  rw [exists_two_iff (by decide) (by decide)]
  decide

example : ∃ f : Nat → Bool, HasPeriod f 24 ∧ ExactlyTwo 24 f := by
  rw [exists_two_iff (by decide) (by decide)]
  decide

example (f : Nat → Bool) (hp : HasPeriod f 24)
    (hmin : ∀ d, 0 < d → HasPeriod f d → 24 ≤ d) : defectCount 24 f ≠ 2 := by
  intro hc
  obtain ⟨h,A,B,hh,h3,_⟩ := (least_period_classification (by decide) (by decide) hp hmin).mp
    ((count_eq_two_iff (by decide) hp).mp hc)
  omega

example (m : Nat) (hm : 0 < m) (h3 : m%3=0) (f : Nat → Bool)
    (hp : HasPeriod f m) (hne : f 1 ≠ f 2) : 3 ≤ defectCount m f :=
  three_le_of_separates_off_three hm h3 hp (by decide) (by decide) hne
