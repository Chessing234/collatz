import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0916

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6886. -/
theorem bounds_13_6886 : exactInterval 13 6886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6886 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6886) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6886 : oddCount 6886 13 = 6 ∧ acceleratedOrbit 13 6886 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6886 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6886) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6886.1, data_13_6886.2]

/-- Complete interval computation for depth 13, residue 6887. -/
theorem bounds_13_6887 : exactInterval 13 6887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6887 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6887) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6887 : oddCount 6887 13 = 11 ∧ acceleratedOrbit 13 6887 = 148958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6887 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6887) = 3 ^ 11 * m + 148958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6887.1, data_13_6887.2]

/-- Complete interval computation for depth 13, residue 6888. -/
theorem bounds_13_6888 : exactInterval 13 6888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6888 : oddCount 6888 13 = 5 ∧ acceleratedOrbit 13 6888 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6888) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6888.1, data_13_6888.2]

/-- Complete interval computation for depth 13, residue 6889. -/
theorem bounds_13_6889 : exactInterval 13 6889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6889 : oddCount 6889 13 = 8 ∧ acceleratedOrbit 13 6889 = 5519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6889) = 3 ^ 8 * m + 5519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6889.1, data_13_6889.2]

/-- Complete interval computation for depth 13, residue 6890. -/
theorem bounds_13_6890 : exactInterval 13 6890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6890 : oddCount 6890 13 = 5 ∧ acceleratedOrbit 13 6890 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6890) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6890.1, data_13_6890.2]

/-- Complete interval computation for depth 13, residue 6891. -/
theorem bounds_13_6891 : exactInterval 13 6891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6891 : oddCount 6891 13 = 8 ∧ acceleratedOrbit 13 6891 = 5521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6891) = 3 ^ 8 * m + 5521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6891.1, data_13_6891.2]

/-- Complete interval computation for depth 13, residue 6892. -/
theorem bounds_13_6892 : exactInterval 13 6892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6892 : oddCount 6892 13 = 6 ∧ acceleratedOrbit 13 6892 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6892) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6892.1, data_13_6892.2]

/-- Complete interval computation for depth 13, residue 6893. -/
theorem bounds_13_6893 : exactInterval 13 6893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6893 : oddCount 6893 13 = 6 ∧ acceleratedOrbit 13 6893 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6893) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6893.1, data_13_6893.2]

/-- Complete interval computation for depth 13, residue 6894. -/
theorem bounds_13_6894 : exactInterval 13 6894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6894 : oddCount 6894 13 = 6 ∧ acceleratedOrbit 13 6894 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6894) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6894.1, data_13_6894.2]

/-- Complete interval computation for depth 13, residue 6895. -/
theorem bounds_13_6895 : exactInterval 13 6895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6895 : oddCount 6895 13 = 10 ∧ acceleratedOrbit 13 6895 = 49709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6895) = 3 ^ 10 * m + 49709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6895.1, data_13_6895.2]

/-- Complete interval computation for depth 13, residue 6896. -/
theorem bounds_13_6896 : exactInterval 13 6896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6896 : oddCount 6896 13 = 5 ∧ acceleratedOrbit 13 6896 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6896) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6896.1, data_13_6896.2]

/-- Complete interval computation for depth 13, residue 6897. -/
theorem bounds_13_6897 : exactInterval 13 6897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6897 : oddCount 6897 13 = 5 ∧ acceleratedOrbit 13 6897 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6897) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6897.1, data_13_6897.2]

/-- Complete interval computation for depth 13, residue 6898. -/
theorem bounds_13_6898 : exactInterval 13 6898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6898 : oddCount 6898 13 = 8 ∧ acceleratedOrbit 13 6898 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6898) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6898.1, data_13_6898.2]

/-- Complete interval computation for depth 13, residue 6899. -/
theorem bounds_13_6899 : exactInterval 13 6899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6899 : oddCount 6899 13 = 8 ∧ acceleratedOrbit 13 6899 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6899) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6899.1, data_13_6899.2]

/-- Complete interval computation for depth 13, residue 6900. -/
theorem bounds_13_6900 : exactInterval 13 6900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6900 : oddCount 6900 13 = 5 ∧ acceleratedOrbit 13 6900 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6900) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6900.1, data_13_6900.2]

end Collatz.Research.StoppingAtlas.Batch0916
