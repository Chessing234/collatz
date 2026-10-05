import Collatz.Strategy.PeriodicDefectAmplification

#print axioms Collatz.PeriodicDefectTransport.mass_pull
#print axioms Collatz.PeriodicDefectTransport.two_step_growth
#print axioms Collatz.PeriodicDefectTransport.labelPulls_orbit
#print axioms Collatz.PeriodicDefectTransport.error_pulls
#print axioms Collatz.PeriodicDefectTransport.defectTower_eq_massTower
#print axioms Collatz.PeriodicDefectTransport.defect_one_step
#print axioms Collatz.PeriodicDefectTransport.defect_linear_growth
#print axioms Collatz.PeriodicDefectTransport.defect_plateau_iff_bounded
#print axioms Collatz.PeriodicDefectTransport.defect_bounded_iff_core_invariant
#print axioms Collatz.PeriodicDefectTransport.defect_plateau_forever
#print axioms Collatz.PeriodicDefectAmplification.weighted_pull
#print axioms Collatz.PeriodicDefectAmplification.weighted_iterate
#print axioms Collatz.PeriodicDefectAmplification.bound_of_table
#print axioms Collatz.PeriodicDefectAmplification.four_certificate
#print axioms Collatz.PeriodicDefectAmplification.four_coefficient_optimal
#print axioms Collatz.PeriodicDefectAmplification.three_coefficient_le_one
#print axioms Collatz.PeriodicDefectAmplification.growth_of_certificate
#print axioms Collatz.PeriodicDefectAmplification.finite_certificate_amplifies
#print axioms Collatz.PeriodicDefectAmplification.defect_growth_of_table
#print axioms Collatz.PeriodicDefectAmplification.defect_exponential_growth
#print axioms Collatz.PeriodicDefectAmplification.defect_dichotomy
#print axioms Collatz.PeriodicDefectAmplification.defect_exact_doubling
#print axioms Collatz.PeriodicDefectAmplification.defect_dichotomy_all

namespace Collatz.PeriodicDefectAudit
open PeriodicRigidity PeriodicDefectMinimum PeriodicDefectTransport
open PeriodicDefectAmplification
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def spike9 (n : Nat) : Bool := n%9=1
theorem spike9_period : HasPeriod spike9 9 := by intro n; simp [spike9]

-- The factor three in the two-step increment is attained by an actual label.
example : defectCount 9 spike9=3 := by decide
example : coreDefects 9 spike9=3 := by decide
example : defectTower 9 spike9 2=12 := by decide
example : defectTower 9 spike9 2=defectCount 9 spike9+3*coreDefects 9 spike9 := by decide
example (k : Nat) : 4^k*3 ≤ defectTower 9 spike9 (4*k) :=
  defect_exponential_growth (by decide) spike9_period k

-- A nonconstant label really can have a constant defect tower.
def mult3 (n : Nat) : Bool := n%3=0
theorem mult3_period : HasPeriod mult3 3 := by intro n; simp [mult3]
example : mult3 0 ≠ mult3 1 := by decide
example : defectCount 3 mult3=1 := by decide
example : coreDefects 3 mult3=0 := by decide
example (k : Nat) : defectTower 3 mult3 k=1 :=
  defect_plateau_forever (by decide) (by decide) mult3_period (by decide) k

-- Check the transfer certificate's boundary witnesses independently of its table.
example : weights 0 1=1 ∧ weights 1 1=1 ∧ weights 2 5=1 ∧ weights 3 7=1 := by decide
example : weights 4 4=4 := by decide

-- The optimal four-step certificate is attained by a genuine periodic weight.
def delta243 (n : Nat) : Nat := if n%243=4 then 1 else 0
theorem delta243_period : HasPeriod delta243 243 := by intro n; simp [delta243]
example : coreMass 243 delta243=1 := by decide
example : coreTower 243 delta243 4=4 := by
  rw [weighted_iterate 4 delta243_period (by decide)]
  decide

-- An arbitrary period divisible by three, not restricted to powers of three.
example {g : Nat → Nat} (hp : HasPeriod g 30) (k : Nat) :
    4^k*coreMass 30 g ≤ coreTower 30 g (4*k) :=
  finite_certificate_amplifies 4 4 four_certificate (by decide) hp k

example {f : Nat → Bool} (hp : HasPeriod f 10) (k : Nat) :
    defectTower 10 f k=2^k*defectCount 10 f :=
  defect_exact_doubling (by decide) (by decide) hp k
end Collatz.PeriodicDefectAudit
