import Collatz.Strategy.PeriodicBranchEmbedding

#print axioms Collatz.PeriodicBranchEmbedding.branch0
#print axioms Collatz.PeriodicBranchEmbedding.choose_branch
#print axioms Collatz.PeriodicBranchEmbedding.four_preimages
#print axioms Collatz.PeriodicBranchEmbedding.weighted_fibers
#print axioms Collatz.PeriodicBranchEmbedding.core_fourfold
#print axioms Collatz.PeriodicBranchEmbedding.core_exponential
#print axioms Collatz.PeriodicBranchEmbedding.defect_exponential
#print axioms Collatz.PeriodicBranchEmbedding.defect_dichotomy
#print axioms Collatz.PeriodicBranchEmbedding.two_step_test
#print axioms Collatz.PeriodicBranchEmbedding.transfer_sharp
#print axioms Collatz.PeriodicBranchEmbedding.fourfold_optimal
#print axioms Collatz.PeriodicBranchEmbedding.three_steps_insufficient

open Collatz.PeriodicRigidity Collatz.PeriodicDefectMinimum
open Collatz.PeriodicDefectTransport Collatz.PeriodicBranchEmbedding

private def stableLabel (n : Nat) : Bool := n%3==0
private def growingLabel (n : Nat) : Bool := n%3==1

private theorem stable_period : HasPeriod stableLabel 3 := by
  intro n
  simp [stableLabel]

private theorem growing_period : HasPeriod growingLabel 3 := by
  intro n
  simp [growingLabel]

example : defectCount 3 stableLabel=1 ∧ coreDefects 3 stableLabel=0 := by decide
example : defectCount 3 growingLabel=3 ∧ coreDefects 3 growingLabel=3 := by decide

example (k : Nat) : defectTower 3 stableLabel k=1 := by
  have h := defect_plateau_forever (by decide : 0<3) (by decide : 3%3=0)
    stable_period (by decide) k
  exact h

example (j : Nat) : 4^j*3 ≤ defectTower 3 growingLabel (4*j) :=
  defect_exponential (by decide) (by decide) growing_period j

example : coreTower 9 (fun n => if n%9=7 then 1 else 0) 3=1 :=
  transfer_sharp.2.1

example : coreTower 9 (fun n => if n%9=7 then 1 else 0) 4=4 :=
  transfer_sharp.2.2
