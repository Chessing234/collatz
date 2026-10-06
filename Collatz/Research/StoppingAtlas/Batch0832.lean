import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0832

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5596. -/
theorem bounds_13_5596 : exactInterval 13 5596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5596 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5596) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5596 : oddCount 5596 13 = 6 ∧ acceleratedOrbit 13 5596 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5596 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5596) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5596.1, data_13_5596.2]

/-- Complete interval computation for depth 13, residue 5597. -/
theorem bounds_13_5597 : exactInterval 13 5597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5597 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5597) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5597 : oddCount 5597 13 = 6 ∧ acceleratedOrbit 13 5597 = 499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5597 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5597) = 3 ^ 6 * m + 499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5597.1, data_13_5597.2]

/-- Complete interval computation for depth 13, residue 5598. -/
theorem bounds_13_5598 : exactInterval 13 5598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5598 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5598) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5598 : oddCount 5598 13 = 9 ∧ acceleratedOrbit 13 5598 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5598 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5598) = 3 ^ 9 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5598.1, data_13_5598.2]

/-- Complete interval computation for depth 13, residue 5599. -/
theorem bounds_13_5599 : exactInterval 13 5599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5599 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5599) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5599 : oddCount 5599 13 = 9 ∧ acceleratedOrbit 13 5599 = 13456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5599 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5599) = 3 ^ 9 * m + 13456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5599.1, data_13_5599.2]

/-- Complete interval computation for depth 13, residue 5600. -/
theorem bounds_13_5600 : exactInterval 13 5600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5600 : oddCount 5600 13 = 5 ∧ acceleratedOrbit 13 5600 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5600) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5600.1, data_13_5600.2]

/-- Complete interval computation for depth 13, residue 5601. -/
theorem bounds_13_5601 : exactInterval 13 5601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5601 : oddCount 5601 13 = 7 ∧ acceleratedOrbit 13 5601 = 1496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5601) = 3 ^ 7 * m + 1496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5601.1, data_13_5601.2]

/-- Complete interval computation for depth 13, residue 5602. -/
theorem bounds_13_5602 : exactInterval 13 5602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5602 : oddCount 5602 13 = 4 ∧ acceleratedOrbit 13 5602 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5602) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5602.1, data_13_5602.2]

/-- Complete interval computation for depth 13, residue 5603. -/
theorem bounds_13_5603 : exactInterval 13 5603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5603 : oddCount 5603 13 = 4 ∧ acceleratedOrbit 13 5603 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5603) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5603.1, data_13_5603.2]

/-- Complete interval computation for depth 13, residue 5604. -/
theorem bounds_13_5604 : exactInterval 13 5604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5604 : oddCount 5604 13 = 8 ∧ acceleratedOrbit 13 5604 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5604) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5604.1, data_13_5604.2]

/-- Complete interval computation for depth 13, residue 5605. -/
theorem bounds_13_5605 : exactInterval 13 5605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5605 : oddCount 5605 13 = 8 ∧ acceleratedOrbit 13 5605 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5605) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5605.1, data_13_5605.2]

/-- Complete interval computation for depth 13, residue 5606. -/
theorem bounds_13_5606 : exactInterval 13 5606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5606 : oddCount 5606 13 = 8 ∧ acceleratedOrbit 13 5606 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5606) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5606.1, data_13_5606.2]

/-- Complete interval computation for depth 13, residue 5607. -/
theorem bounds_13_5607 : exactInterval 13 5607 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5607) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5607 : oddCount 5607 13 = 8 ∧ acceleratedOrbit 13 5607 = 4492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5607) = 3 ^ 8 * m + 4492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5607.1, data_13_5607.2]

/-- Complete interval computation for depth 13, residue 5608. -/
theorem bounds_13_5608 : exactInterval 13 5608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5608 : oddCount 5608 13 = 5 ∧ acceleratedOrbit 13 5608 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5608) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5608.1, data_13_5608.2]

/-- Complete interval computation for depth 13, residue 5609. -/
theorem bounds_13_5609 : exactInterval 13 5609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5609 : oddCount 5609 13 = 10 ∧ acceleratedOrbit 13 5609 = 40445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5609) = 3 ^ 10 * m + 40445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5609.1, data_13_5609.2]

/-- Complete interval computation for depth 13, residue 5610. -/
theorem bounds_13_5610 : exactInterval 13 5610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5610 : oddCount 5610 13 = 5 ∧ acceleratedOrbit 13 5610 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5610) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5610.1, data_13_5610.2]

end Collatz.Research.StoppingAtlas.Batch0832
