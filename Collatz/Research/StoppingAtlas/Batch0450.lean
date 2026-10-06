import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0450

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3824. -/
theorem bounds_12_3824 : exactInterval 12 3824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3824 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3824) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3824 : oddCount 3824 12 = 7 ∧ acceleratedOrbit 12 3824 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3824 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3824) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3824.1, data_12_3824.2]

/-- Complete interval computation for depth 12, residue 3825. -/
theorem bounds_12_3825 : exactInterval 12 3825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3825 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3825) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3825 : oddCount 3825 12 = 4 ∧ acceleratedOrbit 12 3825 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3825 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3825) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3825.1, data_12_3825.2]

/-- Complete interval computation for depth 12, residue 3826. -/
theorem bounds_12_3826 : exactInterval 12 3826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3826 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3826) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3826 : oddCount 3826 12 = 7 ∧ acceleratedOrbit 12 3826 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3826 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3826) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3826.1, data_12_3826.2]

/-- Complete interval computation for depth 12, residue 3827. -/
theorem bounds_12_3827 : exactInterval 12 3827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3827 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3827) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3827 : oddCount 3827 12 = 7 ∧ acceleratedOrbit 12 3827 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3827 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3827) = 3 ^ 7 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3827.1, data_12_3827.2]

/-- Complete interval computation for depth 12, residue 3828. -/
theorem bounds_12_3828 : exactInterval 12 3828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3828 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3828) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3828 : oddCount 3828 12 = 7 ∧ acceleratedOrbit 12 3828 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3828 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3828) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3828.1, data_12_3828.2]

/-- Complete interval computation for depth 12, residue 3829. -/
theorem bounds_12_3829 : exactInterval 12 3829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3829 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3829) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3829 : oddCount 3829 12 = 7 ∧ acceleratedOrbit 12 3829 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3829 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3829) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3829.1, data_12_3829.2]

/-- Complete interval computation for depth 12, residue 3830. -/
theorem bounds_12_3830 : exactInterval 12 3830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3830 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3830) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3830 : oddCount 3830 12 = 7 ∧ acceleratedOrbit 12 3830 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3830 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3830) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3830.1, data_12_3830.2]

/-- Complete interval computation for depth 12, residue 3831. -/
theorem bounds_12_3831 : exactInterval 12 3831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3831 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3831) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3831 : oddCount 3831 12 = 7 ∧ acceleratedOrbit 12 3831 = 2047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3831 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3831) = 3 ^ 7 * m + 2047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3831.1, data_12_3831.2]

/-- Complete interval computation for depth 12, residue 3832. -/
theorem bounds_12_3832 : exactInterval 12 3832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3832 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3832) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3832 : oddCount 3832 12 = 7 ∧ acceleratedOrbit 12 3832 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3832 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3832) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3832.1, data_12_3832.2]

/-- Complete interval computation for depth 12, residue 3833. -/
theorem bounds_12_3833 : exactInterval 12 3833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3833 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3833) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3833 : oddCount 3833 12 = 6 ∧ acceleratedOrbit 12 3833 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3833 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3833) = 3 ^ 6 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3833.1, data_12_3833.2]

/-- Complete interval computation for depth 12, residue 3834. -/
theorem bounds_12_3834 : exactInterval 12 3834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3834 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3834) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3834 : oddCount 3834 12 = 7 ∧ acceleratedOrbit 12 3834 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3834 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3834) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3834.1, data_12_3834.2]

/-- Complete interval computation for depth 12, residue 3835. -/
theorem bounds_12_3835 : exactInterval 12 3835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3835 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3835) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3835 : oddCount 3835 12 = 8 ∧ acceleratedOrbit 12 3835 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3835 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3835) = 3 ^ 8 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3835.1, data_12_3835.2]

/-- Complete interval computation for depth 12, residue 3836. -/
theorem bounds_12_3836 : exactInterval 12 3836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3836 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3836) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3836 : oddCount 3836 12 = 8 ∧ acceleratedOrbit 12 3836 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3836 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3836) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3836.1, data_12_3836.2]

/-- Complete interval computation for depth 12, residue 3837. -/
theorem bounds_12_3837 : exactInterval 12 3837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3837 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3837) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3837 : oddCount 3837 12 = 8 ∧ acceleratedOrbit 12 3837 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3837 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3837) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3837.1, data_12_3837.2]

/-- Complete interval computation for depth 12, residue 3838. -/
theorem bounds_12_3838 : exactInterval 12 3838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3838 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3838) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3838 : oddCount 3838 12 = 8 ∧ acceleratedOrbit 12 3838 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3838 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3838) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3838.1, data_12_3838.2]

/-- Complete interval computation for depth 12, residue 3839. -/
theorem bounds_12_3839 : exactInterval 12 3839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3839 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3839) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3839 : oddCount 3839 12 = 11 ∧ acceleratedOrbit 12 3839 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3839 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3839) = 3 ^ 11 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3839.1, data_12_3839.2]

end Collatz.Research.StoppingAtlas.Batch0450
