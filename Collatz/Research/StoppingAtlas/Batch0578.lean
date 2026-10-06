import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0578

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1694. -/
theorem bounds_13_1694 : exactInterval 13 1694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1694 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1694) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1694 : oddCount 1694 13 = 6 ∧ acceleratedOrbit 13 1694 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1694 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1694) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1694.1, data_13_1694.2]

/-- Complete interval computation for depth 13, residue 1695. -/
theorem bounds_13_1695 : exactInterval 13 1695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1695 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1695) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1695 : oddCount 1695 13 = 10 ∧ acceleratedOrbit 13 1695 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1695 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1695) = 3 ^ 10 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1695.1, data_13_1695.2]

/-- Complete interval computation for depth 13, residue 1696. -/
theorem bounds_13_1696 : exactInterval 13 1696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1696 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1696) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1696 : oddCount 1696 13 = 2 ∧ acceleratedOrbit 13 1696 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1696 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1696) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1696.1, data_13_1696.2]

/-- Complete interval computation for depth 13, residue 1697. -/
theorem bounds_13_1697 : exactInterval 13 1697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1697 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1697) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1697 : oddCount 1697 13 = 7 ∧ acceleratedOrbit 13 1697 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1697 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1697) = 3 ^ 7 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1697.1, data_13_1697.2]

/-- Complete interval computation for depth 13, residue 1698. -/
theorem bounds_13_1698 : exactInterval 13 1698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1698 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1698) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1698 : oddCount 1698 13 = 8 ∧ acceleratedOrbit 13 1698 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1698 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1698) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1698.1, data_13_1698.2]

/-- Complete interval computation for depth 13, residue 1699. -/
theorem bounds_13_1699 : exactInterval 13 1699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1699 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1699) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1699 : oddCount 1699 13 = 8 ∧ acceleratedOrbit 13 1699 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1699 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1699) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1699.1, data_13_1699.2]

/-- Complete interval computation for depth 13, residue 1700. -/
theorem bounds_13_1700 : exactInterval 13 1700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1700 : oddCount 1700 13 = 8 ∧ acceleratedOrbit 13 1700 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1700) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1700.1, data_13_1700.2]

/-- Complete interval computation for depth 13, residue 1701. -/
theorem bounds_13_1701 : exactInterval 13 1701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1701 : oddCount 1701 13 = 8 ∧ acceleratedOrbit 13 1701 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1701) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1701.1, data_13_1701.2]

/-- Complete interval computation for depth 13, residue 1702. -/
theorem bounds_13_1702 : exactInterval 13 1702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1702 : oddCount 1702 13 = 8 ∧ acceleratedOrbit 13 1702 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1702) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1702.1, data_13_1702.2]

/-- Complete interval computation for depth 13, residue 1703. -/
theorem bounds_13_1703 : exactInterval 13 1703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1703 : oddCount 1703 13 = 7 ∧ acceleratedOrbit 13 1703 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1703) = 3 ^ 7 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1703.1, data_13_1703.2]

/-- Complete interval computation for depth 13, residue 1704. -/
theorem bounds_13_1704 : exactInterval 13 1704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1704 : oddCount 1704 13 = 2 ∧ acceleratedOrbit 13 1704 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1704) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1704.1, data_13_1704.2]

/-- Complete interval computation for depth 13, residue 1705. -/
theorem bounds_13_1705 : exactInterval 13 1705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1705 : oddCount 1705 13 = 10 ∧ acceleratedOrbit 13 1705 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1705) = 3 ^ 10 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1705.1, data_13_1705.2]

/-- Complete interval computation for depth 13, residue 1706. -/
theorem bounds_13_1706 : exactInterval 13 1706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1706 : oddCount 1706 13 = 2 ∧ acceleratedOrbit 13 1706 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1706) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1706.1, data_13_1706.2]

/-- Complete interval computation for depth 13, residue 1707. -/
theorem bounds_13_1707 : exactInterval 13 1707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1707 : oddCount 1707 13 = 8 ∧ acceleratedOrbit 13 1707 = 1370 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1707) = 3 ^ 8 * m + 1370 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1707.1, data_13_1707.2]

/-- Complete interval computation for depth 13, residue 1708. -/
theorem bounds_13_1708 : exactInterval 13 1708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1708 : oddCount 1708 13 = 8 ∧ acceleratedOrbit 13 1708 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1708) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1708.1, data_13_1708.2]

/-- Complete interval computation for depth 13, residue 1709. -/
theorem bounds_13_1709 : exactInterval 13 1709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1709 : oddCount 1709 13 = 8 ∧ acceleratedOrbit 13 1709 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1709) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1709.1, data_13_1709.2]

end Collatz.Research.StoppingAtlas.Batch0578
