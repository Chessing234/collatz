import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0178

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1694. -/
theorem bounds_11_1694 : exactInterval 11 1694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1694 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1694) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1694 : oddCount 1694 11 = 6 ∧ acceleratedOrbit 11 1694 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1694 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1694) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1694.1, data_11_1694.2]

/-- Complete interval computation for depth 11, residue 1695. -/
theorem bounds_11_1695 : exactInterval 11 1695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1695 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1695) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1695 : oddCount 1695 11 = 9 ∧ acceleratedOrbit 11 1695 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1695 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1695) = 3 ^ 9 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1695.1, data_11_1695.2]

/-- Complete interval computation for depth 11, residue 1696. -/
theorem bounds_11_1696 : exactInterval 11 1696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1696 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1696) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1696 : oddCount 1696 11 = 2 ∧ acceleratedOrbit 11 1696 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1696 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1696) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1696.1, data_11_1696.2]

/-- Complete interval computation for depth 11, residue 1697. -/
theorem bounds_11_1697 : exactInterval 11 1697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1697 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1697) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1697 : oddCount 1697 11 = 6 ∧ acceleratedOrbit 11 1697 = 605 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1697 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1697) = 3 ^ 6 * m + 605 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1697.1, data_11_1697.2]

/-- Complete interval computation for depth 11, residue 1698. -/
theorem bounds_11_1698 : exactInterval 11 1698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1698 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1698) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1698 : oddCount 1698 11 = 6 ∧ acceleratedOrbit 11 1698 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1698 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1698) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1698.1, data_11_1698.2]

/-- Complete interval computation for depth 11, residue 1699. -/
theorem bounds_11_1699 : exactInterval 11 1699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1699 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1699) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1699 : oddCount 1699 11 = 6 ∧ acceleratedOrbit 11 1699 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1699 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1699) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1699.1, data_11_1699.2]

/-- Complete interval computation for depth 11, residue 1700. -/
theorem bounds_11_1700 : exactInterval 11 1700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1700 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1700) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1700 : oddCount 1700 11 = 7 ∧ acceleratedOrbit 11 1700 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1700 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1700) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1700.1, data_11_1700.2]

/-- Complete interval computation for depth 11, residue 1701. -/
theorem bounds_11_1701 : exactInterval 11 1701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1701 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1701) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1701 : oddCount 1701 11 = 7 ∧ acceleratedOrbit 11 1701 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1701 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1701) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1701.1, data_11_1701.2]

/-- Complete interval computation for depth 11, residue 1702. -/
theorem bounds_11_1702 : exactInterval 11 1702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1702 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1702) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1702 : oddCount 1702 11 = 7 ∧ acceleratedOrbit 11 1702 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1702 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1702) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1702.1, data_11_1702.2]

/-- Complete interval computation for depth 11, residue 1703. -/
theorem bounds_11_1703 : exactInterval 11 1703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1703 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1703) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1703 : oddCount 1703 11 = 7 ∧ acceleratedOrbit 11 1703 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1703 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1703) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1703.1, data_11_1703.2]

/-- Complete interval computation for depth 11, residue 1704. -/
theorem bounds_11_1704 : exactInterval 11 1704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1704 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1704) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1704 : oddCount 1704 11 = 2 ∧ acceleratedOrbit 11 1704 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1704 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1704) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1704.1, data_11_1704.2]

/-- Complete interval computation for depth 11, residue 1705. -/
theorem bounds_11_1705 : exactInterval 11 1705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1705 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1705) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1705 : oddCount 1705 11 = 9 ∧ acceleratedOrbit 11 1705 = 16402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1705 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1705) = 3 ^ 9 * m + 16402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1705.1, data_11_1705.2]

/-- Complete interval computation for depth 11, residue 1706. -/
theorem bounds_11_1706 : exactInterval 11 1706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1706 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1706) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1706 : oddCount 1706 11 = 2 ∧ acceleratedOrbit 11 1706 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1706 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1706) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1706.1, data_11_1706.2]

/-- Complete interval computation for depth 11, residue 1707. -/
theorem bounds_11_1707 : exactInterval 11 1707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1707 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1707) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1707 : oddCount 1707 11 = 7 ∧ acceleratedOrbit 11 1707 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1707 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1707) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1707.1, data_11_1707.2]

/-- Complete interval computation for depth 11, residue 1708. -/
theorem bounds_11_1708 : exactInterval 11 1708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1708 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1708) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1708 : oddCount 1708 11 = 6 ∧ acceleratedOrbit 11 1708 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1708 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1708) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1708.1, data_11_1708.2]

/-- Complete interval computation for depth 11, residue 1709. -/
theorem bounds_11_1709 : exactInterval 11 1709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1709 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1709) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1709 : oddCount 1709 11 = 6 ∧ acceleratedOrbit 11 1709 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1709 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1709) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1709.1, data_11_1709.2]

end Collatz.Research.StoppingAtlas.Batch0178
