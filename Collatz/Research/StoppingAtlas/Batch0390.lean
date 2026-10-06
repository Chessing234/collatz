import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0390

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2903. -/
theorem bounds_12_2903 : exactInterval 12 2903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2903 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2903) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2903 : oddCount 2903 12 = 7 ∧ acceleratedOrbit 12 2903 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2903 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2903) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2903.1, data_12_2903.2]

/-- Complete interval computation for depth 12, residue 2904. -/
theorem bounds_12_2904 : exactInterval 12 2904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2904 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2904) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2904 : oddCount 2904 12 = 5 ∧ acceleratedOrbit 12 2904 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2904 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2904) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2904.1, data_12_2904.2]

/-- Complete interval computation for depth 12, residue 2905. -/
theorem bounds_12_2905 : exactInterval 12 2905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2905 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2905) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2905 : oddCount 2905 12 = 5 ∧ acceleratedOrbit 12 2905 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2905 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2905) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2905.1, data_12_2905.2]

/-- Complete interval computation for depth 12, residue 2906. -/
theorem bounds_12_2906 : exactInterval 12 2906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2906 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2906) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2906 : oddCount 2906 12 = 5 ∧ acceleratedOrbit 12 2906 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2906 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2906) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2906.1, data_12_2906.2]

/-- Complete interval computation for depth 12, residue 2907. -/
theorem bounds_12_2907 : exactInterval 12 2907 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2907 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2907) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2907 : oddCount 2907 12 = 7 ∧ acceleratedOrbit 12 2907 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2907 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2907) = 3 ^ 7 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2907.1, data_12_2907.2]

/-- Complete interval computation for depth 12, residue 2908. -/
theorem bounds_12_2908 : exactInterval 12 2908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2908 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2908) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2908 : oddCount 2908 12 = 5 ∧ acceleratedOrbit 12 2908 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2908 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2908) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2908.1, data_12_2908.2]

/-- Complete interval computation for depth 12, residue 2909. -/
theorem bounds_12_2909 : exactInterval 12 2909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2909 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2909) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2909 : oddCount 2909 12 = 5 ∧ acceleratedOrbit 12 2909 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2909 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2909) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2909.1, data_12_2909.2]

/-- Complete interval computation for depth 12, residue 2910. -/
theorem bounds_12_2910 : exactInterval 12 2910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2910 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2910) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2910 : oddCount 2910 12 = 7 ∧ acceleratedOrbit 12 2910 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2910 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2910) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2910.1, data_12_2910.2]

/-- Complete interval computation for depth 12, residue 2911. -/
theorem bounds_12_2911 : exactInterval 12 2911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2911 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2911) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2911 : oddCount 2911 12 = 7 ∧ acceleratedOrbit 12 2911 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2911 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2911) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2911.1, data_12_2911.2]

/-- Complete interval computation for depth 12, residue 2912. -/
theorem bounds_12_2912 : exactInterval 12 2912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2912 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2912) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2912 : oddCount 2912 12 = 5 ∧ acceleratedOrbit 12 2912 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2912 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2912) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2912.1, data_12_2912.2]

/-- Complete interval computation for depth 12, residue 2913. -/
theorem bounds_12_2913 : exactInterval 12 2913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2913 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2913) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2913 : oddCount 2913 12 = 9 ∧ acceleratedOrbit 12 2913 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2913 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2913) = 3 ^ 9 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2913.1, data_12_2913.2]

/-- Complete interval computation for depth 12, residue 2914. -/
theorem bounds_12_2914 : exactInterval 12 2914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2914 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2914) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2914 : oddCount 2914 12 = 4 ∧ acceleratedOrbit 12 2914 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2914 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2914) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2914.1, data_12_2914.2]

/-- Complete interval computation for depth 12, residue 2915. -/
theorem bounds_12_2915 : exactInterval 12 2915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2915 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2915) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2915 : oddCount 2915 12 = 4 ∧ acceleratedOrbit 12 2915 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2915 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2915) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2915.1, data_12_2915.2]

/-- Complete interval computation for depth 12, residue 2916. -/
theorem bounds_12_2916 : exactInterval 12 2916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2916 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2916) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2916 : oddCount 2916 12 = 4 ∧ acceleratedOrbit 12 2916 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2916 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2916) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2916.1, data_12_2916.2]

/-- Complete interval computation for depth 12, residue 2917. -/
theorem bounds_12_2917 : exactInterval 12 2917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2917 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2917) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2917 : oddCount 2917 12 = 4 ∧ acceleratedOrbit 12 2917 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2917 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2917) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2917.1, data_12_2917.2]

end Collatz.Research.StoppingAtlas.Batch0390
