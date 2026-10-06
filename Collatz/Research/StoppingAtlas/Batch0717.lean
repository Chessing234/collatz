import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0717

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3829. -/
theorem bounds_13_3829 : exactInterval 13 3829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3829 : oddCount 3829 13 = 8 ∧ acceleratedOrbit 13 3829 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3829) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3829.1, data_13_3829.2]

/-- Complete interval computation for depth 13, residue 3830. -/
theorem bounds_13_3830 : exactInterval 13 3830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3830 : oddCount 3830 13 = 8 ∧ acceleratedOrbit 13 3830 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3830) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3830.1, data_13_3830.2]

/-- Complete interval computation for depth 13, residue 3831. -/
theorem bounds_13_3831 : exactInterval 13 3831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3831 : oddCount 3831 13 = 8 ∧ acceleratedOrbit 13 3831 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3831) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3831.1, data_13_3831.2]

/-- Complete interval computation for depth 13, residue 3832. -/
theorem bounds_13_3832 : exactInterval 13 3832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3832 : oddCount 3832 13 = 8 ∧ acceleratedOrbit 13 3832 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3832) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3832.1, data_13_3832.2]

/-- Complete interval computation for depth 13, residue 3833. -/
theorem bounds_13_3833 : exactInterval 13 3833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3833 : oddCount 3833 13 = 7 ∧ acceleratedOrbit 13 3833 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3833) = 3 ^ 7 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3833.1, data_13_3833.2]

/-- Complete interval computation for depth 13, residue 3834. -/
theorem bounds_13_3834 : exactInterval 13 3834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3834 : oddCount 3834 13 = 8 ∧ acceleratedOrbit 13 3834 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3834) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3834.1, data_13_3834.2]

/-- Complete interval computation for depth 13, residue 3835. -/
theorem bounds_13_3835 : exactInterval 13 3835 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3835) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3835 : oddCount 3835 13 = 8 ∧ acceleratedOrbit 13 3835 = 3073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3835) = 3 ^ 8 * m + 3073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3835.1, data_13_3835.2]

/-- Complete interval computation for depth 13, residue 3836. -/
theorem bounds_13_3836 : exactInterval 13 3836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3836 : oddCount 3836 13 = 9 ∧ acceleratedOrbit 13 3836 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3836) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3836.1, data_13_3836.2]

/-- Complete interval computation for depth 13, residue 3837. -/
theorem bounds_13_3837 : exactInterval 13 3837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3837 : oddCount 3837 13 = 9 ∧ acceleratedOrbit 13 3837 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3837) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3837.1, data_13_3837.2]

/-- Complete interval computation for depth 13, residue 3838. -/
theorem bounds_13_3838 : exactInterval 13 3838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3838 : oddCount 3838 13 = 9 ∧ acceleratedOrbit 13 3838 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3838) = 3 ^ 9 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3838.1, data_13_3838.2]

/-- Complete interval computation for depth 13, residue 3839. -/
theorem bounds_13_3839 : exactInterval 13 3839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3839 : oddCount 3839 13 = 11 ∧ acceleratedOrbit 13 3839 = 83038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3839) = 3 ^ 11 * m + 83038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3839.1, data_13_3839.2]

/-- Complete interval computation for depth 13, residue 3840. -/
theorem bounds_13_3840 : exactInterval 13 3840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3840 : oddCount 3840 13 = 4 ∧ acceleratedOrbit 13 3840 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3840) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3840.1, data_13_3840.2]

/-- Complete interval computation for depth 13, residue 3841. -/
theorem bounds_13_3841 : exactInterval 13 3841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3841 : oddCount 3841 13 = 4 ∧ acceleratedOrbit 13 3841 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3841) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3841.1, data_13_3841.2]

/-- Complete interval computation for depth 13, residue 3842. -/
theorem bounds_13_3842 : exactInterval 13 3842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3842 : oddCount 3842 13 = 7 ∧ acceleratedOrbit 13 3842 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3842) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3842.1, data_13_3842.2]

/-- Complete interval computation for depth 13, residue 3843. -/
theorem bounds_13_3843 : exactInterval 13 3843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3843 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3843) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3843 : oddCount 3843 13 = 7 ∧ acceleratedOrbit 13 3843 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3843 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3843) = 3 ^ 7 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3843.1, data_13_3843.2]

/-- Complete interval computation for depth 13, residue 3844. -/
theorem bounds_13_3844 : exactInterval 13 3844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3844 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3844) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3844 : oddCount 3844 13 = 6 ∧ acceleratedOrbit 13 3844 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3844 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3844) = 3 ^ 6 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3844.1, data_13_3844.2]

end Collatz.Research.StoppingAtlas.Batch0717
