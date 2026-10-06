import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0782

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4828. -/
theorem bounds_13_4828 : exactInterval 13 4828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4828 : oddCount 4828 13 = 7 ∧ acceleratedOrbit 13 4828 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4828) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4828.1, data_13_4828.2]

/-- Complete interval computation for depth 13, residue 4829. -/
theorem bounds_13_4829 : exactInterval 13 4829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4829 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4829) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4829 : oddCount 4829 13 = 7 ∧ acceleratedOrbit 13 4829 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4829 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4829) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4829.1, data_13_4829.2]

/-- Complete interval computation for depth 13, residue 4830. -/
theorem bounds_13_4830 : exactInterval 13 4830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4830 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4830) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4830 : oddCount 4830 13 = 6 ∧ acceleratedOrbit 13 4830 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4830 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4830) = 3 ^ 6 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4830.1, data_13_4830.2]

/-- Complete interval computation for depth 13, residue 4831. -/
theorem bounds_13_4831 : exactInterval 13 4831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4831 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4831) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4831 : oddCount 4831 13 = 6 ∧ acceleratedOrbit 13 4831 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4831 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4831) = 3 ^ 6 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4831.1, data_13_4831.2]

/-- Complete interval computation for depth 13, residue 4832. -/
theorem bounds_13_4832 : exactInterval 13 4832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4832 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4832) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4832 : oddCount 4832 13 = 3 ∧ acceleratedOrbit 13 4832 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4832 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4832) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4832.1, data_13_4832.2]

/-- Complete interval computation for depth 13, residue 4833. -/
theorem bounds_13_4833 : exactInterval 13 4833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4833 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4833) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4833 : oddCount 4833 13 = 10 ∧ acceleratedOrbit 13 4833 = 34856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4833 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4833) = 3 ^ 10 * m + 34856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4833.1, data_13_4833.2]

/-- Complete interval computation for depth 13, residue 4834. -/
theorem bounds_13_4834 : exactInterval 13 4834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4834 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4834) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4834 : oddCount 4834 13 = 3 ∧ acceleratedOrbit 13 4834 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4834 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4834) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4834.1, data_13_4834.2]

/-- Complete interval computation for depth 13, residue 4835. -/
theorem bounds_13_4835 : exactInterval 13 4835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4835 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4835) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4835 : oddCount 4835 13 = 3 ∧ acceleratedOrbit 13 4835 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4835 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4835) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4835.1, data_13_4835.2]

/-- Complete interval computation for depth 13, residue 4836. -/
theorem bounds_13_4836 : exactInterval 13 4836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4836 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4836) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4836 : oddCount 4836 13 = 7 ∧ acceleratedOrbit 13 4836 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4836 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4836) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4836.1, data_13_4836.2]

/-- Complete interval computation for depth 13, residue 4837. -/
theorem bounds_13_4837 : exactInterval 13 4837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4837 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4837) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4837 : oddCount 4837 13 = 7 ∧ acceleratedOrbit 13 4837 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4837 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4837) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4837.1, data_13_4837.2]

/-- Complete interval computation for depth 13, residue 4838. -/
theorem bounds_13_4838 : exactInterval 13 4838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4838 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4838) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4838 : oddCount 4838 13 = 7 ∧ acceleratedOrbit 13 4838 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4838 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4838) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4838.1, data_13_4838.2]

/-- Complete interval computation for depth 13, residue 4839. -/
theorem bounds_13_4839 : exactInterval 13 4839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4839 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4839) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4839 : oddCount 4839 13 = 9 ∧ acceleratedOrbit 13 4839 = 11630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4839 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4839) = 3 ^ 9 * m + 11630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4839.1, data_13_4839.2]

/-- Complete interval computation for depth 13, residue 4840. -/
theorem bounds_13_4840 : exactInterval 13 4840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4840 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4840) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4840 : oddCount 4840 13 = 3 ∧ acceleratedOrbit 13 4840 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4840 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4840) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4840.1, data_13_4840.2]

/-- Complete interval computation for depth 13, residue 4841. -/
theorem bounds_13_4841 : exactInterval 13 4841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4841 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4841) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4841 : oddCount 4841 13 = 10 ∧ acceleratedOrbit 13 4841 = 34910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4841 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4841) = 3 ^ 10 * m + 34910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4841.1, data_13_4841.2]

/-- Complete interval computation for depth 13, residue 4842. -/
theorem bounds_13_4842 : exactInterval 13 4842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4842 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4842) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4842 : oddCount 4842 13 = 3 ∧ acceleratedOrbit 13 4842 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4842 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4842) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4842.1, data_13_4842.2]

end Collatz.Research.StoppingAtlas.Batch0782
