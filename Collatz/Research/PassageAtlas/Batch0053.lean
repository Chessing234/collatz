import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0053

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 1703. -/
theorem bounds_15_1703 : exactInterval 15 1703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1703 : oddCount 1703 15 = 9 ∧ acceleratedOrbit 15 1703 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1703) = 3 ^ 9 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1703.1, data_15_1703.2]

/-- Complete interval computation for depth 15, residue 1704. -/
theorem bounds_15_1704 : exactInterval 15 1704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1704 : oddCount 1704 15 = 3 ∧ acceleratedOrbit 15 1704 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1704) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1704.1, data_15_1704.2]

/-- Complete interval computation for depth 15, residue 1705. -/
theorem bounds_15_1705 : exactInterval 15 1705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1705 : oddCount 1705 15 = 11 ∧ acceleratedOrbit 15 1705 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1705) = 3 ^ 11 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1705.1, data_15_1705.2]

/-- Complete interval computation for depth 15, residue 1706. -/
theorem bounds_15_1706 : exactInterval 15 1706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1706 : oddCount 1706 15 = 3 ∧ acceleratedOrbit 15 1706 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1706) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1706.1, data_15_1706.2]

/-- Complete interval computation for depth 15, residue 1707. -/
theorem bounds_15_1707 : exactInterval 15 1707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1707 : oddCount 1707 15 = 9 ∧ acceleratedOrbit 15 1707 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1707) = 3 ^ 9 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1707.1, data_15_1707.2]

/-- Complete interval computation for depth 15, residue 1708. -/
theorem bounds_15_1708 : exactInterval 15 1708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1708 : oddCount 1708 15 = 8 ∧ acceleratedOrbit 15 1708 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1708) = 3 ^ 8 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1708.1, data_15_1708.2]

/-- Complete interval computation for depth 15, residue 1709. -/
theorem bounds_15_1709 : exactInterval 15 1709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1709 : oddCount 1709 15 = 8 ∧ acceleratedOrbit 15 1709 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1709) = 3 ^ 8 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1709.1, data_15_1709.2]

/-- Complete interval computation for depth 15, residue 1710. -/
theorem bounds_15_1710 : exactInterval 15 1710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1710 : oddCount 1710 15 = 8 ∧ acceleratedOrbit 15 1710 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1710) = 3 ^ 8 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1710.1, data_15_1710.2]

/-- Complete interval computation for depth 15, residue 1711. -/
theorem bounds_15_1711 : exactInterval 15 1711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1711 : oddCount 1711 15 = 8 ∧ acceleratedOrbit 15 1711 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1711) = 3 ^ 8 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1711.1, data_15_1711.2]

/-- Complete interval computation for depth 15, residue 1712. -/
theorem bounds_15_1712 : exactInterval 15 1712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1712 : oddCount 1712 15 = 8 ∧ acceleratedOrbit 15 1712 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1712) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1712.1, data_15_1712.2]

/-- Complete interval computation for depth 15, residue 1713. -/
theorem bounds_15_1713 : exactInterval 15 1713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1713 : oddCount 1713 15 = 5 ∧ acceleratedOrbit 15 1713 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1713) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1713.1, data_15_1713.2]

/-- Complete interval computation for depth 15, residue 1714. -/
theorem bounds_15_1714 : exactInterval 15 1714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1714 : oddCount 1714 15 = 5 ∧ acceleratedOrbit 15 1714 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1714) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1714.1, data_15_1714.2]

/-- Complete interval computation for depth 15, residue 1715. -/
theorem bounds_15_1715 : exactInterval 15 1715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1715 : oddCount 1715 15 = 5 ∧ acceleratedOrbit 15 1715 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1715) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1715.1, data_15_1715.2]

/-- Complete interval computation for depth 15, residue 1716. -/
theorem bounds_15_1716 : exactInterval 15 1716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1716 : oddCount 1716 15 = 8 ∧ acceleratedOrbit 15 1716 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1716) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1716.1, data_15_1716.2]

/-- Complete interval computation for depth 15, residue 1717. -/
theorem bounds_15_1717 : exactInterval 15 1717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1717 : oddCount 1717 15 = 8 ∧ acceleratedOrbit 15 1717 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1717) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1717.1, data_15_1717.2]

/-- Complete interval computation for depth 15, residue 1718. -/
theorem bounds_15_1718 : exactInterval 15 1718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1718 : oddCount 1718 15 = 10 ∧ acceleratedOrbit 15 1718 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1718) = 3 ^ 10 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1718.1, data_15_1718.2]

/-- Complete interval computation for depth 15, residue 1719. -/
theorem bounds_15_1719 : exactInterval 15 1719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1719 : oddCount 1719 15 = 10 ∧ acceleratedOrbit 15 1719 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1719) = 3 ^ 10 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1719.1, data_15_1719.2]

/-- Complete interval computation for depth 15, residue 1720. -/
theorem bounds_15_1720 : exactInterval 15 1720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1720 : oddCount 1720 15 = 8 ∧ acceleratedOrbit 15 1720 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1720) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1720.1, data_15_1720.2]

/-- Complete interval computation for depth 15, residue 1721. -/
theorem bounds_15_1721 : exactInterval 15 1721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1721 : oddCount 1721 15 = 8 ∧ acceleratedOrbit 15 1721 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1721) = 3 ^ 8 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1721.1, data_15_1721.2]

/-- Complete interval computation for depth 15, residue 1722. -/
theorem bounds_15_1722 : exactInterval 15 1722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1722 : oddCount 1722 15 = 8 ∧ acceleratedOrbit 15 1722 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1722) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1722.1, data_15_1722.2]

/-- Complete interval computation for depth 15, residue 1723. -/
theorem bounds_15_1723 : exactInterval 15 1723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1723 : oddCount 1723 15 = 8 ∧ acceleratedOrbit 15 1723 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1723) = 3 ^ 8 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1723.1, data_15_1723.2]

/-- Complete interval computation for depth 15, residue 1724. -/
theorem bounds_15_1724 : exactInterval 15 1724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1724 : oddCount 1724 15 = 7 ∧ acceleratedOrbit 15 1724 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1724) = 3 ^ 7 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1724.1, data_15_1724.2]

/-- Complete interval computation for depth 15, residue 1725. -/
theorem bounds_15_1725 : exactInterval 15 1725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1725 : oddCount 1725 15 = 7 ∧ acceleratedOrbit 15 1725 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1725) = 3 ^ 7 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1725.1, data_15_1725.2]

/-- Complete interval computation for depth 15, residue 1726. -/
theorem bounds_15_1726 : exactInterval 15 1726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1726 : oddCount 1726 15 = 7 ∧ acceleratedOrbit 15 1726 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1726) = 3 ^ 7 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1726.1, data_15_1726.2]

/-- Complete interval computation for depth 15, residue 1727. -/
theorem bounds_15_1727 : exactInterval 15 1727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1727 : oddCount 1727 15 = 8 ∧ acceleratedOrbit 15 1727 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1727) = 3 ^ 8 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1727.1, data_15_1727.2]

/-- Complete interval computation for depth 15, residue 1728. -/
theorem bounds_15_1728 : exactInterval 15 1728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1728 : oddCount 1728 15 = 7 ∧ acceleratedOrbit 15 1728 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1728) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1728.1, data_15_1728.2]

/-- Complete interval computation for depth 15, residue 1729. -/
theorem bounds_15_1729 : exactInterval 15 1729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1729 : oddCount 1729 15 = 8 ∧ acceleratedOrbit 15 1729 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1729) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1729.1, data_15_1729.2]

/-- Complete interval computation for depth 15, residue 1730. -/
theorem bounds_15_1730 : exactInterval 15 1730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1730 : oddCount 1730 15 = 9 ∧ acceleratedOrbit 15 1730 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1730) = 3 ^ 9 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1730.1, data_15_1730.2]

/-- Complete interval computation for depth 15, residue 1731. -/
theorem bounds_15_1731 : exactInterval 15 1731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1731 : oddCount 1731 15 = 9 ∧ acceleratedOrbit 15 1731 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1731) = 3 ^ 9 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1731.1, data_15_1731.2]

/-- Complete interval computation for depth 15, residue 1732. -/
theorem bounds_15_1732 : exactInterval 15 1732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1732 : oddCount 1732 15 = 6 ∧ acceleratedOrbit 15 1732 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1732) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1732.1, data_15_1732.2]

/-- Complete interval computation for depth 15, residue 1733. -/
theorem bounds_15_1733 : exactInterval 15 1733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1733 : oddCount 1733 15 = 6 ∧ acceleratedOrbit 15 1733 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1733) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1733.1, data_15_1733.2]

/-- Complete interval computation for depth 15, residue 1734. -/
theorem bounds_15_1734 : exactInterval 15 1734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1734 : oddCount 1734 15 = 6 ∧ acceleratedOrbit 15 1734 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1734) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1734.1, data_15_1734.2]

/-- Complete interval computation for depth 15, residue 1735. -/
theorem bounds_15_1735 : exactInterval 15 1735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_1735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 1735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_1735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_1735 : oddCount 1735 15 = 8 ∧ acceleratedOrbit 15 1735 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_1735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 1735) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_1735.1, data_15_1735.2]

end Collatz.Research.PassageAtlas.Batch0053
