import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0912

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6824. -/
theorem bounds_13_6824 : exactInterval 13 6824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6824 : oddCount 6824 13 = 2 ∧ acceleratedOrbit 13 6824 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6824) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6824.1, data_13_6824.2]

/-- Complete interval computation for depth 13, residue 6825. -/
theorem bounds_13_6825 : exactInterval 13 6825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6825 : oddCount 6825 13 = 11 ∧ acceleratedOrbit 13 6825 = 147622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6825) = 3 ^ 11 * m + 147622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6825.1, data_13_6825.2]

/-- Complete interval computation for depth 13, residue 6826. -/
theorem bounds_13_6826 : exactInterval 13 6826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6826 : oddCount 6826 13 = 2 ∧ acceleratedOrbit 13 6826 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6826) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6826.1, data_13_6826.2]

/-- Complete interval computation for depth 13, residue 6827. -/
theorem bounds_13_6827 : exactInterval 13 6827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6827 : oddCount 6827 13 = 8 ∧ acceleratedOrbit 13 6827 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6827) = 3 ^ 8 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6827.1, data_13_6827.2]

/-- Complete interval computation for depth 13, residue 6828. -/
theorem bounds_13_6828 : exactInterval 13 6828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6828 : oddCount 6828 13 = 7 ∧ acceleratedOrbit 13 6828 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6828) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6828.1, data_13_6828.2]

/-- Complete interval computation for depth 13, residue 6829. -/
theorem bounds_13_6829 : exactInterval 13 6829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6829 : oddCount 6829 13 = 7 ∧ acceleratedOrbit 13 6829 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6829) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6829.1, data_13_6829.2]

/-- Complete interval computation for depth 13, residue 6830. -/
theorem bounds_13_6830 : exactInterval 13 6830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6830 : oddCount 6830 13 = 7 ∧ acceleratedOrbit 13 6830 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6830) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6830.1, data_13_6830.2]

/-- Complete interval computation for depth 13, residue 6831. -/
theorem bounds_13_6831 : exactInterval 13 6831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6831 : oddCount 6831 13 = 6 ∧ acceleratedOrbit 13 6831 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6831) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6831.1, data_13_6831.2]

/-- Complete interval computation for depth 13, residue 6832. -/
theorem bounds_13_6832 : exactInterval 13 6832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6832 : oddCount 6832 13 = 6 ∧ acceleratedOrbit 13 6832 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6832) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6832.1, data_13_6832.2]

/-- Complete interval computation for depth 13, residue 6833. -/
theorem bounds_13_6833 : exactInterval 13 6833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6833 : oddCount 6833 13 = 5 ∧ acceleratedOrbit 13 6833 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6833) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6833.1, data_13_6833.2]

/-- Complete interval computation for depth 13, residue 6834. -/
theorem bounds_13_6834 : exactInterval 13 6834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6834 : oddCount 6834 13 = 5 ∧ acceleratedOrbit 13 6834 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6834) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6834.1, data_13_6834.2]

/-- Complete interval computation for depth 13, residue 6835. -/
theorem bounds_13_6835 : exactInterval 13 6835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6835) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6835 : oddCount 6835 13 = 5 ∧ acceleratedOrbit 13 6835 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6835) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6835.1, data_13_6835.2]

/-- Complete interval computation for depth 13, residue 6836. -/
theorem bounds_13_6836 : exactInterval 13 6836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6836 : oddCount 6836 13 = 6 ∧ acceleratedOrbit 13 6836 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6836) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6836.1, data_13_6836.2]

/-- Complete interval computation for depth 13, residue 6837. -/
theorem bounds_13_6837 : exactInterval 13 6837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6837 : oddCount 6837 13 = 6 ∧ acceleratedOrbit 13 6837 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6837) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6837.1, data_13_6837.2]

/-- Complete interval computation for depth 13, residue 6838. -/
theorem bounds_13_6838 : exactInterval 13 6838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6838 : oddCount 6838 13 = 8 ∧ acceleratedOrbit 13 6838 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6838) = 3 ^ 8 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6838.1, data_13_6838.2]

/-- Complete interval computation for depth 13, residue 6839. -/
theorem bounds_13_6839 : exactInterval 13 6839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6839 : oddCount 6839 13 = 8 ∧ acceleratedOrbit 13 6839 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6839) = 3 ^ 8 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6839.1, data_13_6839.2]

end Collatz.Research.StoppingAtlas.Batch0912
