import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0307

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1628. -/
theorem bounds_12_1628 : exactInterval 12 1628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1628 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1628) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1628 : oddCount 1628 12 = 5 ∧ acceleratedOrbit 12 1628 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1628 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1628) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1628.1, data_12_1628.2]

/-- Complete interval computation for depth 12, residue 1629. -/
theorem bounds_12_1629 : exactInterval 12 1629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1629 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1629) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1629 : oddCount 1629 12 = 5 ∧ acceleratedOrbit 12 1629 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1629 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1629) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1629.1, data_12_1629.2]

/-- Complete interval computation for depth 12, residue 1630. -/
theorem bounds_12_1630 : exactInterval 12 1630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1630 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1630) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1630 : oddCount 1630 12 = 7 ∧ acceleratedOrbit 12 1630 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1630 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1630) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1630.1, data_12_1630.2]

/-- Complete interval computation for depth 12, residue 1631. -/
theorem bounds_12_1631 : exactInterval 12 1631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1631 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1631) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1631 : oddCount 1631 12 = 7 ∧ acceleratedOrbit 12 1631 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1631 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1631) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1631.1, data_12_1631.2]

/-- Complete interval computation for depth 12, residue 1632. -/
theorem bounds_12_1632 : exactInterval 12 1632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1632 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1632) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1632 : oddCount 1632 12 = 3 ∧ acceleratedOrbit 12 1632 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1632 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1632) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1632.1, data_12_1632.2]

/-- Complete interval computation for depth 12, residue 1633. -/
theorem bounds_12_1633 : exactInterval 12 1633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1633 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1633) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1633 : oddCount 1633 12 = 5 ∧ acceleratedOrbit 12 1633 = 97 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1633 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1633) = 3 ^ 5 * m + 97 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1633.1, data_12_1633.2]

/-- Complete interval computation for depth 12, residue 1634. -/
theorem bounds_12_1634 : exactInterval 12 1634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1634 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1634) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1634 : oddCount 1634 12 = 5 ∧ acceleratedOrbit 12 1634 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1634 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1634) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1634.1, data_12_1634.2]

/-- Complete interval computation for depth 12, residue 1635. -/
theorem bounds_12_1635 : exactInterval 12 1635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1635 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1635) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1635 : oddCount 1635 12 = 5 ∧ acceleratedOrbit 12 1635 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1635 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1635) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1635.1, data_12_1635.2]

/-- Complete interval computation for depth 12, residue 1636. -/
theorem bounds_12_1636 : exactInterval 12 1636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1636 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1636) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1636 : oddCount 1636 12 = 5 ∧ acceleratedOrbit 12 1636 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1636 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1636) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1636.1, data_12_1636.2]

/-- Complete interval computation for depth 12, residue 1637. -/
theorem bounds_12_1637 : exactInterval 12 1637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1637 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1637) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1637 : oddCount 1637 12 = 5 ∧ acceleratedOrbit 12 1637 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1637 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1637) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1637.1, data_12_1637.2]

/-- Complete interval computation for depth 12, residue 1638. -/
theorem bounds_12_1638 : exactInterval 12 1638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1638 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1638) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1638 : oddCount 1638 12 = 5 ∧ acceleratedOrbit 12 1638 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1638 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1638) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1638.1, data_12_1638.2]

/-- Complete interval computation for depth 12, residue 1639. -/
theorem bounds_12_1639 : exactInterval 12 1639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1639 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1639) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1639 : oddCount 1639 12 = 9 ∧ acceleratedOrbit 12 1639 = 7883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1639 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1639) = 3 ^ 9 * m + 7883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1639.1, data_12_1639.2]

/-- Complete interval computation for depth 12, residue 1640. -/
theorem bounds_12_1640 : exactInterval 12 1640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1640 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1640) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1640 : oddCount 1640 12 = 3 ∧ acceleratedOrbit 12 1640 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1640 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1640) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1640.1, data_12_1640.2]

/-- Complete interval computation for depth 12, residue 1641. -/
theorem bounds_12_1641 : exactInterval 12 1641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1641 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1641) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1641 : oddCount 1641 12 = 8 ∧ acceleratedOrbit 12 1641 = 2632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1641 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1641) = 3 ^ 8 * m + 2632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1641.1, data_12_1641.2]

/-- Complete interval computation for depth 12, residue 1642. -/
theorem bounds_12_1642 : exactInterval 12 1642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1642 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1642) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1642 : oddCount 1642 12 = 3 ∧ acceleratedOrbit 12 1642 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1642 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1642) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1642.1, data_12_1642.2]

end Collatz.Research.StoppingAtlas.Batch0307
