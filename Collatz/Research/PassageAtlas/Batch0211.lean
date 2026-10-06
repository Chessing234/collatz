import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0211

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6881. -/
theorem bounds_15_6881 : exactInterval 15 6881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6881 : oddCount 6881 15 = 9 ∧ acceleratedOrbit 15 6881 = 4135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6881) = 3 ^ 9 * m + 4135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6881.1, data_15_6881.2]

/-- Complete interval computation for depth 15, residue 6882. -/
theorem bounds_15_6882 : exactInterval 15 6882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6882 : oddCount 6882 15 = 6 ∧ acceleratedOrbit 15 6882 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6882) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6882.1, data_15_6882.2]

/-- Complete interval computation for depth 15, residue 6883. -/
theorem bounds_15_6883 : exactInterval 15 6883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6883 : oddCount 6883 15 = 6 ∧ acceleratedOrbit 15 6883 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6883) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6883.1, data_15_6883.2]

/-- Complete interval computation for depth 15, residue 6884. -/
theorem bounds_15_6884 : exactInterval 15 6884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6884 : oddCount 6884 15 = 7 ∧ acceleratedOrbit 15 6884 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6884) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6884.1, data_15_6884.2]

/-- Complete interval computation for depth 15, residue 6885. -/
theorem bounds_15_6885 : exactInterval 15 6885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6885 : oddCount 6885 15 = 7 ∧ acceleratedOrbit 15 6885 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6885) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6885.1, data_15_6885.2]

/-- Complete interval computation for depth 15, residue 6886. -/
theorem bounds_15_6886 : exactInterval 15 6886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6886 : oddCount 6886 15 = 7 ∧ acceleratedOrbit 15 6886 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6886) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6886.1, data_15_6886.2]

/-- Complete interval computation for depth 15, residue 6887. -/
theorem bounds_15_6887 : exactInterval 15 6887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6887 : oddCount 6887 15 = 12 ∧ acceleratedOrbit 15 6887 = 111719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6887) = 3 ^ 12 * m + 111719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6887.1, data_15_6887.2]

/-- Complete interval computation for depth 15, residue 6888. -/
theorem bounds_15_6888 : exactInterval 15 6888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6888 : oddCount 6888 15 = 6 ∧ acceleratedOrbit 15 6888 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6888) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6888.1, data_15_6888.2]

/-- Complete interval computation for depth 15, residue 6889. -/
theorem bounds_15_6889 : exactInterval 15 6889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6889 : oddCount 6889 15 = 10 ∧ acceleratedOrbit 15 6889 = 12419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6889) = 3 ^ 10 * m + 12419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6889.1, data_15_6889.2]

/-- Complete interval computation for depth 15, residue 6890. -/
theorem bounds_15_6890 : exactInterval 15 6890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6890 : oddCount 6890 15 = 6 ∧ acceleratedOrbit 15 6890 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6890) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6890.1, data_15_6890.2]

/-- Complete interval computation for depth 15, residue 6891. -/
theorem bounds_15_6891 : exactInterval 15 6891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6891 : oddCount 6891 15 = 9 ∧ acceleratedOrbit 15 6891 = 4141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6891) = 3 ^ 9 * m + 4141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6891.1, data_15_6891.2]

/-- Complete interval computation for depth 15, residue 6892. -/
theorem bounds_15_6892 : exactInterval 15 6892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6892 : oddCount 6892 15 = 7 ∧ acceleratedOrbit 15 6892 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6892) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6892.1, data_15_6892.2]

/-- Complete interval computation for depth 15, residue 6893. -/
theorem bounds_15_6893 : exactInterval 15 6893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6893 : oddCount 6893 15 = 7 ∧ acceleratedOrbit 15 6893 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6893) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6893.1, data_15_6893.2]

/-- Complete interval computation for depth 15, residue 6894. -/
theorem bounds_15_6894 : exactInterval 15 6894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6894 : oddCount 6894 15 = 7 ∧ acceleratedOrbit 15 6894 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6894) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6894.1, data_15_6894.2]

/-- Complete interval computation for depth 15, residue 6895. -/
theorem bounds_15_6895 : exactInterval 15 6895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6895 : oddCount 6895 15 = 11 ∧ acceleratedOrbit 15 6895 = 37282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6895) = 3 ^ 11 * m + 37282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6895.1, data_15_6895.2]

/-- Complete interval computation for depth 15, residue 6896. -/
theorem bounds_15_6896 : exactInterval 15 6896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6896 : oddCount 6896 15 = 6 ∧ acceleratedOrbit 15 6896 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6896) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6896.1, data_15_6896.2]

/-- Complete interval computation for depth 15, residue 6897. -/
theorem bounds_15_6897 : exactInterval 15 6897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6897 : oddCount 6897 15 = 6 ∧ acceleratedOrbit 15 6897 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6897) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6897.1, data_15_6897.2]

/-- Complete interval computation for depth 15, residue 6898. -/
theorem bounds_15_6898 : exactInterval 15 6898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6898 : oddCount 6898 15 = 8 ∧ acceleratedOrbit 15 6898 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6898) = 3 ^ 8 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6898.1, data_15_6898.2]

/-- Complete interval computation for depth 15, residue 6899. -/
theorem bounds_15_6899 : exactInterval 15 6899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6899 : oddCount 6899 15 = 8 ∧ acceleratedOrbit 15 6899 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6899) = 3 ^ 8 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6899.1, data_15_6899.2]

/-- Complete interval computation for depth 15, residue 6900. -/
theorem bounds_15_6900 : exactInterval 15 6900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6900 : oddCount 6900 15 = 6 ∧ acceleratedOrbit 15 6900 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6900) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6900.1, data_15_6900.2]

/-- Complete interval computation for depth 15, residue 6901. -/
theorem bounds_15_6901 : exactInterval 15 6901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6901 : oddCount 6901 15 = 6 ∧ acceleratedOrbit 15 6901 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6901) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6901.1, data_15_6901.2]

/-- Complete interval computation for depth 15, residue 6902. -/
theorem bounds_15_6902 : exactInterval 15 6902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6902 : oddCount 6902 15 = 7 ∧ acceleratedOrbit 15 6902 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6902) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6902.1, data_15_6902.2]

/-- Complete interval computation for depth 15, residue 6903. -/
theorem bounds_15_6903 : exactInterval 15 6903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6903 : oddCount 6903 15 = 7 ∧ acceleratedOrbit 15 6903 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6903) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6903.1, data_15_6903.2]

/-- Complete interval computation for depth 15, residue 6904. -/
theorem bounds_15_6904 : exactInterval 15 6904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6904 : oddCount 6904 15 = 6 ∧ acceleratedOrbit 15 6904 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6904) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6904.1, data_15_6904.2]

/-- Complete interval computation for depth 15, residue 6905. -/
theorem bounds_15_6905 : exactInterval 15 6905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6905 : oddCount 6905 15 = 9 ∧ acceleratedOrbit 15 6905 = 4151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6905) = 3 ^ 9 * m + 4151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6905.1, data_15_6905.2]

/-- Complete interval computation for depth 15, residue 6906. -/
theorem bounds_15_6906 : exactInterval 15 6906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6906 : oddCount 6906 15 = 6 ∧ acceleratedOrbit 15 6906 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6906) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6906.1, data_15_6906.2]

/-- Complete interval computation for depth 15, residue 6907. -/
theorem bounds_15_6907 : exactInterval 15 6907 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6907) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6907 : oddCount 6907 15 = 9 ∧ acceleratedOrbit 15 6907 = 4150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6907) = 3 ^ 9 * m + 4150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6907.1, data_15_6907.2]

/-- Complete interval computation for depth 15, residue 6908. -/
theorem bounds_15_6908 : exactInterval 15 6908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6908 : oddCount 6908 15 = 8 ∧ acceleratedOrbit 15 6908 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6908) = 3 ^ 8 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6908.1, data_15_6908.2]

/-- Complete interval computation for depth 15, residue 6909. -/
theorem bounds_15_6909 : exactInterval 15 6909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6909 : oddCount 6909 15 = 8 ∧ acceleratedOrbit 15 6909 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6909) = 3 ^ 8 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6909.1, data_15_6909.2]

/-- Complete interval computation for depth 15, residue 6910. -/
theorem bounds_15_6910 : exactInterval 15 6910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6910 : oddCount 6910 15 = 8 ∧ acceleratedOrbit 15 6910 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6910) = 3 ^ 8 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6910.1, data_15_6910.2]

/-- Complete interval computation for depth 15, residue 6911. -/
theorem bounds_15_6911 : exactInterval 15 6911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6911 : oddCount 6911 15 = 12 ∧ acceleratedOrbit 15 6911 = 112103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6911) = 3 ^ 12 * m + 112103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6911.1, data_15_6911.2]

/-- Complete interval computation for depth 15, residue 6912. -/
theorem bounds_15_6912 : exactInterval 15 6912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6912 : oddCount 6912 15 = 6 ∧ acceleratedOrbit 15 6912 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6912) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6912.1, data_15_6912.2]

/-- Complete interval computation for depth 15, residue 6913. -/
theorem bounds_15_6913 : exactInterval 15 6913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6913 : oddCount 6913 15 = 6 ∧ acceleratedOrbit 15 6913 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6913) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6913.1, data_15_6913.2]

end Collatz.Research.PassageAtlas.Batch0211
