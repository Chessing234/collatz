import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0572

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1602. -/
theorem bounds_13_1602 : exactInterval 13 1602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1602 : oddCount 1602 13 = 7 ∧ acceleratedOrbit 13 1602 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1602) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1602.1, data_13_1602.2]

/-- Complete interval computation for depth 13, residue 1603. -/
theorem bounds_13_1603 : exactInterval 13 1603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1603 : oddCount 1603 13 = 7 ∧ acceleratedOrbit 13 1603 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1603) = 3 ^ 7 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1603.1, data_13_1603.2]

/-- Complete interval computation for depth 13, residue 1604. -/
theorem bounds_13_1604 : exactInterval 13 1604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1604 : oddCount 1604 13 = 4 ∧ acceleratedOrbit 13 1604 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1604) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1604.1, data_13_1604.2]

/-- Complete interval computation for depth 13, residue 1605. -/
theorem bounds_13_1605 : exactInterval 13 1605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1605 : oddCount 1605 13 = 4 ∧ acceleratedOrbit 13 1605 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1605) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1605.1, data_13_1605.2]

/-- Complete interval computation for depth 13, residue 1606. -/
theorem bounds_13_1606 : exactInterval 13 1606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1606 : oddCount 1606 13 = 4 ∧ acceleratedOrbit 13 1606 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1606) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1606.1, data_13_1606.2]

/-- Complete interval computation for depth 13, residue 1607. -/
theorem bounds_13_1607 : exactInterval 13 1607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1607) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1607 : oddCount 1607 13 = 8 ∧ acceleratedOrbit 13 1607 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1607) = 3 ^ 8 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1607.1, data_13_1607.2]

/-- Complete interval computation for depth 13, residue 1608. -/
theorem bounds_13_1608 : exactInterval 13 1608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1608 : oddCount 1608 13 = 4 ∧ acceleratedOrbit 13 1608 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1608) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1608.1, data_13_1608.2]

/-- Complete interval computation for depth 13, residue 1609. -/
theorem bounds_13_1609 : exactInterval 13 1609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1609 : oddCount 1609 13 = 8 ∧ acceleratedOrbit 13 1609 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1609) = 3 ^ 8 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1609.1, data_13_1609.2]

/-- Complete interval computation for depth 13, residue 1610. -/
theorem bounds_13_1610 : exactInterval 13 1610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1610 : oddCount 1610 13 = 4 ∧ acceleratedOrbit 13 1610 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1610) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1610.1, data_13_1610.2]

/-- Complete interval computation for depth 13, residue 1611. -/
theorem bounds_13_1611 : exactInterval 13 1611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1611 : oddCount 1611 13 = 4 ∧ acceleratedOrbit 13 1611 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1611) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1611.1, data_13_1611.2]

/-- Complete interval computation for depth 13, residue 1612. -/
theorem bounds_13_1612 : exactInterval 13 1612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1612 : oddCount 1612 13 = 4 ∧ acceleratedOrbit 13 1612 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1612) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1612.1, data_13_1612.2]

/-- Complete interval computation for depth 13, residue 1613. -/
theorem bounds_13_1613 : exactInterval 13 1613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1613 : oddCount 1613 13 = 4 ∧ acceleratedOrbit 13 1613 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1613) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1613.1, data_13_1613.2]

/-- Complete interval computation for depth 13, residue 1614. -/
theorem bounds_13_1614 : exactInterval 13 1614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1614 : oddCount 1614 13 = 9 ∧ acceleratedOrbit 13 1614 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1614) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1614.1, data_13_1614.2]

/-- Complete interval computation for depth 13, residue 1615. -/
theorem bounds_13_1615 : exactInterval 13 1615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1615) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1615 : oddCount 1615 13 = 9 ∧ acceleratedOrbit 13 1615 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1615) = 3 ^ 9 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1615.1, data_13_1615.2]

/-- Complete interval computation for depth 13, residue 1616. -/
theorem bounds_13_1616 : exactInterval 13 1616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1616 : oddCount 1616 13 = 4 ∧ acceleratedOrbit 13 1616 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1616) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1616.1, data_13_1616.2]

end Collatz.Research.StoppingAtlas.Batch0572
