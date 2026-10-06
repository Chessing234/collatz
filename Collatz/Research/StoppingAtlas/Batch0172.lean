import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0172

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1602. -/
theorem bounds_11_1602 : exactInterval 11 1602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1602 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1602) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1602 : oddCount 1602 11 = 5 ∧ acceleratedOrbit 11 1602 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1602 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1602) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1602.1, data_11_1602.2]

/-- Complete interval computation for depth 11, residue 1603. -/
theorem bounds_11_1603 : exactInterval 11 1603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1603 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1603) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1603 : oddCount 1603 11 = 5 ∧ acceleratedOrbit 11 1603 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1603 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1603) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1603.1, data_11_1603.2]

/-- Complete interval computation for depth 11, residue 1604. -/
theorem bounds_11_1604 : exactInterval 11 1604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1604 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1604) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1604 : oddCount 1604 11 = 4 ∧ acceleratedOrbit 11 1604 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1604 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1604) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1604.1, data_11_1604.2]

/-- Complete interval computation for depth 11, residue 1605. -/
theorem bounds_11_1605 : exactInterval 11 1605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1605 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1605) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1605 : oddCount 1605 11 = 4 ∧ acceleratedOrbit 11 1605 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1605 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1605) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1605.1, data_11_1605.2]

/-- Complete interval computation for depth 11, residue 1606. -/
theorem bounds_11_1606 : exactInterval 11 1606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1606 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1606) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1606 : oddCount 1606 11 = 4 ∧ acceleratedOrbit 11 1606 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1606 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1606) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1606.1, data_11_1606.2]

/-- Complete interval computation for depth 11, residue 1607. -/
theorem bounds_11_1607 : exactInterval 11 1607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1607 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1607) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1607 : oddCount 1607 11 = 7 ∧ acceleratedOrbit 11 1607 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1607 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1607) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1607.1, data_11_1607.2]

/-- Complete interval computation for depth 11, residue 1608. -/
theorem bounds_11_1608 : exactInterval 11 1608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1608 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1608) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1608 : oddCount 1608 11 = 4 ∧ acceleratedOrbit 11 1608 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1608 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1608) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1608.1, data_11_1608.2]

/-- Complete interval computation for depth 11, residue 1609. -/
theorem bounds_11_1609 : exactInterval 11 1609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1609 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1609) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1609 : oddCount 1609 11 = 7 ∧ acceleratedOrbit 11 1609 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1609 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1609) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1609.1, data_11_1609.2]

/-- Complete interval computation for depth 11, residue 1610. -/
theorem bounds_11_1610 : exactInterval 11 1610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1610 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1610) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1610 : oddCount 1610 11 = 4 ∧ acceleratedOrbit 11 1610 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1610 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1610) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1610.1, data_11_1610.2]

/-- Complete interval computation for depth 11, residue 1611. -/
theorem bounds_11_1611 : exactInterval 11 1611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1611 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1611) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1611 : oddCount 1611 11 = 4 ∧ acceleratedOrbit 11 1611 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1611 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1611) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1611.1, data_11_1611.2]

/-- Complete interval computation for depth 11, residue 1612. -/
theorem bounds_11_1612 : exactInterval 11 1612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1612 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1612) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1612 : oddCount 1612 11 = 4 ∧ acceleratedOrbit 11 1612 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1612 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1612) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1612.1, data_11_1612.2]

/-- Complete interval computation for depth 11, residue 1613. -/
theorem bounds_11_1613 : exactInterval 11 1613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1613 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1613) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1613 : oddCount 1613 11 = 4 ∧ acceleratedOrbit 11 1613 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1613 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1613) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1613.1, data_11_1613.2]

/-- Complete interval computation for depth 11, residue 1614. -/
theorem bounds_11_1614 : exactInterval 11 1614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1614 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1614) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1614 : oddCount 1614 11 = 7 ∧ acceleratedOrbit 11 1614 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1614 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1614) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1614.1, data_11_1614.2]

/-- Complete interval computation for depth 11, residue 1615. -/
theorem bounds_11_1615 : exactInterval 11 1615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1615 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1615) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1615 : oddCount 1615 11 = 7 ∧ acceleratedOrbit 11 1615 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1615 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1615) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1615.1, data_11_1615.2]

/-- Complete interval computation for depth 11, residue 1616. -/
theorem bounds_11_1616 : exactInterval 11 1616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1616 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1616) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1616 : oddCount 1616 11 = 3 ∧ acceleratedOrbit 11 1616 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1616 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1616) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1616.1, data_11_1616.2]

end Collatz.Research.StoppingAtlas.Batch0172
