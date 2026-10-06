import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0852

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5903. -/
theorem bounds_13_5903 : exactInterval 13 5903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5903 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5903) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5903 : oddCount 5903 13 = 6 ∧ acceleratedOrbit 13 5903 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5903 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5903) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5903.1, data_13_5903.2]

/-- Complete interval computation for depth 13, residue 5904. -/
theorem bounds_13_5904 : exactInterval 13 5904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5904 : oddCount 5904 13 = 3 ∧ acceleratedOrbit 13 5904 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5904) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5904.1, data_13_5904.2]

/-- Complete interval computation for depth 13, residue 5905. -/
theorem bounds_13_5905 : exactInterval 13 5905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5905 : oddCount 5905 13 = 7 ∧ acceleratedOrbit 13 5905 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5905) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5905.1, data_13_5905.2]

/-- Complete interval computation for depth 13, residue 5906. -/
theorem bounds_13_5906 : exactInterval 13 5906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5906 : oddCount 5906 13 = 9 ∧ acceleratedOrbit 13 5906 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5906) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5906.1, data_13_5906.2]

/-- Complete interval computation for depth 13, residue 5907. -/
theorem bounds_13_5907 : exactInterval 13 5907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5907 : oddCount 5907 13 = 9 ∧ acceleratedOrbit 13 5907 = 14201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5907) = 3 ^ 9 * m + 14201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5907.1, data_13_5907.2]

/-- Complete interval computation for depth 13, residue 5908. -/
theorem bounds_13_5908 : exactInterval 13 5908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5908 : oddCount 5908 13 = 3 ∧ acceleratedOrbit 13 5908 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5908) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5908.1, data_13_5908.2]

/-- Complete interval computation for depth 13, residue 5909. -/
theorem bounds_13_5909 : exactInterval 13 5909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5909 : oddCount 5909 13 = 3 ∧ acceleratedOrbit 13 5909 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5909) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5909.1, data_13_5909.2]

/-- Complete interval computation for depth 13, residue 5910. -/
theorem bounds_13_5910 : exactInterval 13 5910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5910 : oddCount 5910 13 = 8 ∧ acceleratedOrbit 13 5910 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5910) = 3 ^ 8 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5910.1, data_13_5910.2]

/-- Complete interval computation for depth 13, residue 5911. -/
theorem bounds_13_5911 : exactInterval 13 5911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5911) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5911 : oddCount 5911 13 = 8 ∧ acceleratedOrbit 13 5911 = 4738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5911) = 3 ^ 8 * m + 4738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5911.1, data_13_5911.2]

/-- Complete interval computation for depth 13, residue 5912. -/
theorem bounds_13_5912 : exactInterval 13 5912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5912 : oddCount 5912 13 = 3 ∧ acceleratedOrbit 13 5912 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5912) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5912.1, data_13_5912.2]

/-- Complete interval computation for depth 13, residue 5913. -/
theorem bounds_13_5913 : exactInterval 13 5913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5913 : oddCount 5913 13 = 9 ∧ acceleratedOrbit 13 5913 = 14215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5913) = 3 ^ 9 * m + 14215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5913.1, data_13_5913.2]

/-- Complete interval computation for depth 13, residue 5914. -/
theorem bounds_13_5914 : exactInterval 13 5914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5914 : oddCount 5914 13 = 3 ∧ acceleratedOrbit 13 5914 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5914) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5914.1, data_13_5914.2]

/-- Complete interval computation for depth 13, residue 5915. -/
theorem bounds_13_5915 : exactInterval 13 5915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5915 : oddCount 5915 13 = 11 ∧ acceleratedOrbit 13 5915 = 127939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5915) = 3 ^ 11 * m + 127939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5915.1, data_13_5915.2]

/-- Complete interval computation for depth 13, residue 5916. -/
theorem bounds_13_5916 : exactInterval 13 5916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5916 : oddCount 5916 13 = 6 ∧ acceleratedOrbit 13 5916 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5916) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5916.1, data_13_5916.2]

/-- Complete interval computation for depth 13, residue 5917. -/
theorem bounds_13_5917 : exactInterval 13 5917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5917 : oddCount 5917 13 = 6 ∧ acceleratedOrbit 13 5917 = 527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5917) = 3 ^ 6 * m + 527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5917.1, data_13_5917.2]

end Collatz.Research.StoppingAtlas.Batch0852
