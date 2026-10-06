import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0847

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5826. -/
theorem bounds_13_5826 : exactInterval 13 5826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5826 : oddCount 5826 13 = 9 ∧ acceleratedOrbit 13 5826 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5826) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5826.1, data_13_5826.2]

/-- Complete interval computation for depth 13, residue 5827. -/
theorem bounds_13_5827 : exactInterval 13 5827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5827 : oddCount 5827 13 = 9 ∧ acceleratedOrbit 13 5827 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5827) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5827.1, data_13_5827.2]

/-- Complete interval computation for depth 13, residue 5828. -/
theorem bounds_13_5828 : exactInterval 13 5828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5828 : oddCount 5828 13 = 4 ∧ acceleratedOrbit 13 5828 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5828) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5828.1, data_13_5828.2]

/-- Complete interval computation for depth 13, residue 5829. -/
theorem bounds_13_5829 : exactInterval 13 5829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5829 : oddCount 5829 13 = 4 ∧ acceleratedOrbit 13 5829 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5829) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5829.1, data_13_5829.2]

/-- Complete interval computation for depth 13, residue 5830. -/
theorem bounds_13_5830 : exactInterval 13 5830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5830 : oddCount 5830 13 = 4 ∧ acceleratedOrbit 13 5830 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5830) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5830.1, data_13_5830.2]

/-- Complete interval computation for depth 13, residue 5831. -/
theorem bounds_13_5831 : exactInterval 13 5831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5831 : oddCount 5831 13 = 5 ∧ acceleratedOrbit 13 5831 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5831) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5831.1, data_13_5831.2]

/-- Complete interval computation for depth 13, residue 5832. -/
theorem bounds_13_5832 : exactInterval 13 5832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5832 : oddCount 5832 13 = 4 ∧ acceleratedOrbit 13 5832 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5832) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5832.1, data_13_5832.2]

/-- Complete interval computation for depth 13, residue 5833. -/
theorem bounds_13_5833 : exactInterval 13 5833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5833 : oddCount 5833 13 = 7 ∧ acceleratedOrbit 13 5833 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5833) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5833.1, data_13_5833.2]

/-- Complete interval computation for depth 13, residue 5834. -/
theorem bounds_13_5834 : exactInterval 13 5834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5834 : oddCount 5834 13 = 4 ∧ acceleratedOrbit 13 5834 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5834) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5834.1, data_13_5834.2]

/-- Complete interval computation for depth 13, residue 5835. -/
theorem bounds_13_5835 : exactInterval 13 5835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5835) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5835 : oddCount 5835 13 = 7 ∧ acceleratedOrbit 13 5835 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5835) = 3 ^ 7 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5835.1, data_13_5835.2]

/-- Complete interval computation for depth 13, residue 5836. -/
theorem bounds_13_5836 : exactInterval 13 5836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5836 : oddCount 5836 13 = 4 ∧ acceleratedOrbit 13 5836 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5836) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5836.1, data_13_5836.2]

/-- Complete interval computation for depth 13, residue 5837. -/
theorem bounds_13_5837 : exactInterval 13 5837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5837 : oddCount 5837 13 = 4 ∧ acceleratedOrbit 13 5837 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5837) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5837.1, data_13_5837.2]

/-- Complete interval computation for depth 13, residue 5838. -/
theorem bounds_13_5838 : exactInterval 13 5838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5838 : oddCount 5838 13 = 9 ∧ acceleratedOrbit 13 5838 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5838) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5838.1, data_13_5838.2]

/-- Complete interval computation for depth 13, residue 5839. -/
theorem bounds_13_5839 : exactInterval 13 5839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5839 : oddCount 5839 13 = 9 ∧ acceleratedOrbit 13 5839 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5839) = 3 ^ 9 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5839.1, data_13_5839.2]

/-- Complete interval computation for depth 13, residue 5840. -/
theorem bounds_13_5840 : exactInterval 13 5840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5840 : oddCount 5840 13 = 5 ∧ acceleratedOrbit 13 5840 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5840) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5840.1, data_13_5840.2]

end Collatz.Research.StoppingAtlas.Batch0847
