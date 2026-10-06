import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0270

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8814. -/
theorem bounds_15_8814 : exactInterval 15 8814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8814 : oddCount 8814 15 = 8 ∧ acceleratedOrbit 15 8814 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8814) = 3 ^ 8 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8814.1, data_15_8814.2]

/-- Complete interval computation for depth 15, residue 8815. -/
theorem bounds_15_8815 : exactInterval 15 8815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8815 : oddCount 8815 15 = 9 ∧ acceleratedOrbit 15 8815 = 5296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8815) = 3 ^ 9 * m + 5296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8815.1, data_15_8815.2]

/-- Complete interval computation for depth 15, residue 8816. -/
theorem bounds_15_8816 : exactInterval 15 8816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8816 : oddCount 8816 15 = 6 ∧ acceleratedOrbit 15 8816 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8816) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8816.1, data_15_8816.2]

/-- Complete interval computation for depth 15, residue 8817. -/
theorem bounds_15_8817 : exactInterval 15 8817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8817 : oddCount 8817 15 = 7 ∧ acceleratedOrbit 15 8817 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8817) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8817.1, data_15_8817.2]

/-- Complete interval computation for depth 15, residue 8818. -/
theorem bounds_15_8818 : exactInterval 15 8818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8818 : oddCount 8818 15 = 10 ∧ acceleratedOrbit 15 8818 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8818) = 3 ^ 10 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8818.1, data_15_8818.2]

/-- Complete interval computation for depth 15, residue 8819. -/
theorem bounds_15_8819 : exactInterval 15 8819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8819 : oddCount 8819 15 = 10 ∧ acceleratedOrbit 15 8819 = 15902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8819) = 3 ^ 10 * m + 15902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8819.1, data_15_8819.2]

/-- Complete interval computation for depth 15, residue 8820. -/
theorem bounds_15_8820 : exactInterval 15 8820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8820 : oddCount 8820 15 = 6 ∧ acceleratedOrbit 15 8820 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8820) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8820.1, data_15_8820.2]

/-- Complete interval computation for depth 15, residue 8821. -/
theorem bounds_15_8821 : exactInterval 15 8821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8821 : oddCount 8821 15 = 6 ∧ acceleratedOrbit 15 8821 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8821) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8821.1, data_15_8821.2]

/-- Complete interval computation for depth 15, residue 8822. -/
theorem bounds_15_8822 : exactInterval 15 8822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8822 : oddCount 8822 15 = 6 ∧ acceleratedOrbit 15 8822 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8822) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8822.1, data_15_8822.2]

/-- Complete interval computation for depth 15, residue 8823. -/
theorem bounds_15_8823 : exactInterval 15 8823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8823 : oddCount 8823 15 = 6 ∧ acceleratedOrbit 15 8823 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8823) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8823.1, data_15_8823.2]

/-- Complete interval computation for depth 15, residue 8824. -/
theorem bounds_15_8824 : exactInterval 15 8824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8824 : oddCount 8824 15 = 6 ∧ acceleratedOrbit 15 8824 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8824) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8824.1, data_15_8824.2]

/-- Complete interval computation for depth 15, residue 8825. -/
theorem bounds_15_8825 : exactInterval 15 8825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8825 : oddCount 8825 15 = 8 ∧ acceleratedOrbit 15 8825 = 1768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8825) = 3 ^ 8 * m + 1768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8825.1, data_15_8825.2]

/-- Complete interval computation for depth 15, residue 8826. -/
theorem bounds_15_8826 : exactInterval 15 8826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8826 : oddCount 8826 15 = 6 ∧ acceleratedOrbit 15 8826 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8826) = 3 ^ 6 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8826.1, data_15_8826.2]

/-- Complete interval computation for depth 15, residue 8827. -/
theorem bounds_15_8827 : exactInterval 15 8827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8827 : oddCount 8827 15 = 9 ∧ acceleratedOrbit 15 8827 = 5305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8827) = 3 ^ 9 * m + 5305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8827.1, data_15_8827.2]

/-- Complete interval computation for depth 15, residue 8828. -/
theorem bounds_15_8828 : exactInterval 15 8828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8828 : oddCount 8828 15 = 11 ∧ acceleratedOrbit 15 8828 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8828) = 3 ^ 11 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8828.1, data_15_8828.2]

/-- Complete interval computation for depth 15, residue 8829. -/
theorem bounds_15_8829 : exactInterval 15 8829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8829 : oddCount 8829 15 = 11 ∧ acceleratedOrbit 15 8829 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8829) = 3 ^ 11 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8829.1, data_15_8829.2]

/-- Complete interval computation for depth 15, residue 8830. -/
theorem bounds_15_8830 : exactInterval 15 8830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8830 : oddCount 8830 15 = 11 ∧ acceleratedOrbit 15 8830 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8830) = 3 ^ 11 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8830.1, data_15_8830.2]

/-- Complete interval computation for depth 15, residue 8831. -/
theorem bounds_15_8831 : exactInterval 15 8831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8831 : oddCount 8831 15 = 11 ∧ acceleratedOrbit 15 8831 = 47747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8831) = 3 ^ 11 * m + 47747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8831.1, data_15_8831.2]

/-- Complete interval computation for depth 15, residue 8832. -/
theorem bounds_15_8832 : exactInterval 15 8832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8832 : oddCount 8832 15 = 3 ∧ acceleratedOrbit 15 8832 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8832) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8832.1, data_15_8832.2]

/-- Complete interval computation for depth 15, residue 8833. -/
theorem bounds_15_8833 : exactInterval 15 8833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8833 : oddCount 8833 15 = 9 ∧ acceleratedOrbit 15 8833 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8833) = 3 ^ 9 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8833.1, data_15_8833.2]

/-- Complete interval computation for depth 15, residue 8834. -/
theorem bounds_15_8834 : exactInterval 15 8834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8834 : oddCount 8834 15 = 7 ∧ acceleratedOrbit 15 8834 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8834) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8834.1, data_15_8834.2]

/-- Complete interval computation for depth 15, residue 8835. -/
theorem bounds_15_8835 : exactInterval 15 8835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8835 : oddCount 8835 15 = 7 ∧ acceleratedOrbit 15 8835 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8835) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8835.1, data_15_8835.2]

/-- Complete interval computation for depth 15, residue 8836. -/
theorem bounds_15_8836 : exactInterval 15 8836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8836 : oddCount 8836 15 = 8 ∧ acceleratedOrbit 15 8836 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8836) = 3 ^ 8 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8836.1, data_15_8836.2]

/-- Complete interval computation for depth 15, residue 8837. -/
theorem bounds_15_8837 : exactInterval 15 8837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8837 : oddCount 8837 15 = 8 ∧ acceleratedOrbit 15 8837 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8837) = 3 ^ 8 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8837.1, data_15_8837.2]

/-- Complete interval computation for depth 15, residue 8838. -/
theorem bounds_15_8838 : exactInterval 15 8838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8838 : oddCount 8838 15 = 8 ∧ acceleratedOrbit 15 8838 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8838) = 3 ^ 8 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8838.1, data_15_8838.2]

/-- Complete interval computation for depth 15, residue 8839. -/
theorem bounds_15_8839 : exactInterval 15 8839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8839 : oddCount 8839 15 = 8 ∧ acceleratedOrbit 15 8839 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8839) = 3 ^ 8 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8839.1, data_15_8839.2]

/-- Complete interval computation for depth 15, residue 8840. -/
theorem bounds_15_8840 : exactInterval 15 8840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8840 : oddCount 8840 15 = 7 ∧ acceleratedOrbit 15 8840 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8840) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8840.1, data_15_8840.2]

/-- Complete interval computation for depth 15, residue 8841. -/
theorem bounds_15_8841 : exactInterval 15 8841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8841 : oddCount 8841 15 = 9 ∧ acceleratedOrbit 15 8841 = 5312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8841) = 3 ^ 9 * m + 5312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8841.1, data_15_8841.2]

/-- Complete interval computation for depth 15, residue 8842. -/
theorem bounds_15_8842 : exactInterval 15 8842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8842 : oddCount 8842 15 = 7 ∧ acceleratedOrbit 15 8842 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8842) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8842.1, data_15_8842.2]

/-- Complete interval computation for depth 15, residue 8843. -/
theorem bounds_15_8843 : exactInterval 15 8843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8843 : oddCount 8843 15 = 8 ∧ acceleratedOrbit 15 8843 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8843) = 3 ^ 8 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8843.1, data_15_8843.2]

/-- Complete interval computation for depth 15, residue 8844. -/
theorem bounds_15_8844 : exactInterval 15 8844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8844 : oddCount 8844 15 = 7 ∧ acceleratedOrbit 15 8844 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8844) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8844.1, data_15_8844.2]

/-- Complete interval computation for depth 15, residue 8845. -/
theorem bounds_15_8845 : exactInterval 15 8845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8845 : oddCount 8845 15 = 7 ∧ acceleratedOrbit 15 8845 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8845) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8845.1, data_15_8845.2]

/-- Complete interval computation for depth 15, residue 8846. -/
theorem bounds_15_8846 : exactInterval 15 8846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8846 : oddCount 8846 15 = 10 ∧ acceleratedOrbit 15 8846 = 15947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8846) = 3 ^ 10 * m + 15947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8846.1, data_15_8846.2]

end Collatz.Research.PassageAtlas.Batch0270
