import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0917

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6901. -/
theorem bounds_13_6901 : exactInterval 13 6901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6901 : oddCount 6901 13 = 5 ∧ acceleratedOrbit 13 6901 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6901) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6901.1, data_13_6901.2]

/-- Complete interval computation for depth 13, residue 6902. -/
theorem bounds_13_6902 : exactInterval 13 6902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6902 : oddCount 6902 13 = 7 ∧ acceleratedOrbit 13 6902 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6902) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6902.1, data_13_6902.2]

/-- Complete interval computation for depth 13, residue 6903. -/
theorem bounds_13_6903 : exactInterval 13 6903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6903) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6903 : oddCount 6903 13 = 7 ∧ acceleratedOrbit 13 6903 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6903) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6903.1, data_13_6903.2]

/-- Complete interval computation for depth 13, residue 6904. -/
theorem bounds_13_6904 : exactInterval 13 6904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6904 : oddCount 6904 13 = 5 ∧ acceleratedOrbit 13 6904 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6904) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6904.1, data_13_6904.2]

/-- Complete interval computation for depth 13, residue 6905. -/
theorem bounds_13_6905 : exactInterval 13 6905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6905 : oddCount 6905 13 = 8 ∧ acceleratedOrbit 13 6905 = 5534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6905) = 3 ^ 8 * m + 5534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6905.1, data_13_6905.2]

/-- Complete interval computation for depth 13, residue 6906. -/
theorem bounds_13_6906 : exactInterval 13 6906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6906 : oddCount 6906 13 = 5 ∧ acceleratedOrbit 13 6906 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6906) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6906.1, data_13_6906.2]

/-- Complete interval computation for depth 13, residue 6907. -/
theorem bounds_13_6907 : exactInterval 13 6907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6907 : oddCount 6907 13 = 9 ∧ acceleratedOrbit 13 6907 = 16600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6907) = 3 ^ 9 * m + 16600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6907.1, data_13_6907.2]

/-- Complete interval computation for depth 13, residue 6908. -/
theorem bounds_13_6908 : exactInterval 13 6908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6908 : oddCount 6908 13 = 8 ∧ acceleratedOrbit 13 6908 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6908) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6908.1, data_13_6908.2]

/-- Complete interval computation for depth 13, residue 6909. -/
theorem bounds_13_6909 : exactInterval 13 6909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6909 : oddCount 6909 13 = 8 ∧ acceleratedOrbit 13 6909 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6909) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6909.1, data_13_6909.2]

/-- Complete interval computation for depth 13, residue 6910. -/
theorem bounds_13_6910 : exactInterval 13 6910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6910 : oddCount 6910 13 = 8 ∧ acceleratedOrbit 13 6910 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6910) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6910.1, data_13_6910.2]

/-- Complete interval computation for depth 13, residue 6911. -/
theorem bounds_13_6911 : exactInterval 13 6911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6911) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6911 : oddCount 6911 13 = 10 ∧ acceleratedOrbit 13 6911 = 49823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6911) = 3 ^ 10 * m + 49823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6911.1, data_13_6911.2]

/-- Complete interval computation for depth 13, residue 6912. -/
theorem bounds_13_6912 : exactInterval 13 6912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6912 : oddCount 6912 13 = 4 ∧ acceleratedOrbit 13 6912 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6912) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6912.1, data_13_6912.2]

/-- Complete interval computation for depth 13, residue 6913. -/
theorem bounds_13_6913 : exactInterval 13 6913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6913 : oddCount 6913 13 = 6 ∧ acceleratedOrbit 13 6913 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6913) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6913.1, data_13_6913.2]

/-- Complete interval computation for depth 13, residue 6914. -/
theorem bounds_13_6914 : exactInterval 13 6914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6914 : oddCount 6914 13 = 6 ∧ acceleratedOrbit 13 6914 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6914) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6914.1, data_13_6914.2]

/-- Complete interval computation for depth 13, residue 6915. -/
theorem bounds_13_6915 : exactInterval 13 6915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6915 : oddCount 6915 13 = 6 ∧ acceleratedOrbit 13 6915 = 616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6915) = 3 ^ 6 * m + 616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6915.1, data_13_6915.2]

/-- Complete interval computation for depth 13, residue 6916. -/
theorem bounds_13_6916 : exactInterval 13 6916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6916 : oddCount 6916 13 = 5 ∧ acceleratedOrbit 13 6916 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6916) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6916.1, data_13_6916.2]

end Collatz.Research.StoppingAtlas.Batch0917
