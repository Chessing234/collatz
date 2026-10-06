import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0657

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2908. -/
theorem bounds_13_2908 : exactInterval 13 2908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2908 : oddCount 2908 13 = 6 ∧ acceleratedOrbit 13 2908 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2908) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2908.1, data_13_2908.2]

/-- Complete interval computation for depth 13, residue 2909. -/
theorem bounds_13_2909 : exactInterval 13 2909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2909 : oddCount 2909 13 = 6 ∧ acceleratedOrbit 13 2909 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2909) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2909.1, data_13_2909.2]

/-- Complete interval computation for depth 13, residue 2910. -/
theorem bounds_13_2910 : exactInterval 13 2910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2910 : oddCount 2910 13 = 7 ∧ acceleratedOrbit 13 2910 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2910) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2910.1, data_13_2910.2]

/-- Complete interval computation for depth 13, residue 2911. -/
theorem bounds_13_2911 : exactInterval 13 2911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2911) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2911 : oddCount 2911 13 = 7 ∧ acceleratedOrbit 13 2911 = 778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2911) = 3 ^ 7 * m + 778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2911.1, data_13_2911.2]

/-- Complete interval computation for depth 13, residue 2912. -/
theorem bounds_13_2912 : exactInterval 13 2912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2912 : oddCount 2912 13 = 6 ∧ acceleratedOrbit 13 2912 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2912) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2912.1, data_13_2912.2]

/-- Complete interval computation for depth 13, residue 2913. -/
theorem bounds_13_2913 : exactInterval 13 2913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2913 : oddCount 2913 13 = 9 ∧ acceleratedOrbit 13 2913 = 7006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2913) = 3 ^ 9 * m + 7006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2913.1, data_13_2913.2]

/-- Complete interval computation for depth 13, residue 2914. -/
theorem bounds_13_2914 : exactInterval 13 2914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2914 : oddCount 2914 13 = 4 ∧ acceleratedOrbit 13 2914 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2914) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2914.1, data_13_2914.2]

/-- Complete interval computation for depth 13, residue 2915. -/
theorem bounds_13_2915 : exactInterval 13 2915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2915 : oddCount 2915 13 = 4 ∧ acceleratedOrbit 13 2915 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2915) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2915.1, data_13_2915.2]

/-- Complete interval computation for depth 13, residue 2916. -/
theorem bounds_13_2916 : exactInterval 13 2916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2916 : oddCount 2916 13 = 4 ∧ acceleratedOrbit 13 2916 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2916) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2916.1, data_13_2916.2]

/-- Complete interval computation for depth 13, residue 2917. -/
theorem bounds_13_2917 : exactInterval 13 2917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2917 : oddCount 2917 13 = 4 ∧ acceleratedOrbit 13 2917 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2917) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2917.1, data_13_2917.2]

/-- Complete interval computation for depth 13, residue 2918. -/
theorem bounds_13_2918 : exactInterval 13 2918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2918 : oddCount 2918 13 = 4 ∧ acceleratedOrbit 13 2918 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2918) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2918.1, data_13_2918.2]

/-- Complete interval computation for depth 13, residue 2919. -/
theorem bounds_13_2919 : exactInterval 13 2919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2919 : oddCount 2919 13 = 10 ∧ acceleratedOrbit 13 2919 = 21050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2919) = 3 ^ 10 * m + 21050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2919.1, data_13_2919.2]

/-- Complete interval computation for depth 13, residue 2920. -/
theorem bounds_13_2920 : exactInterval 13 2920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2920 : oddCount 2920 13 = 6 ∧ acceleratedOrbit 13 2920 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2920) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2920.1, data_13_2920.2]

/-- Complete interval computation for depth 13, residue 2921. -/
theorem bounds_13_2921 : exactInterval 13 2921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2921 : oddCount 2921 13 = 8 ∧ acceleratedOrbit 13 2921 = 2342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2921) = 3 ^ 8 * m + 2342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2921.1, data_13_2921.2]

/-- Complete interval computation for depth 13, residue 2922. -/
theorem bounds_13_2922 : exactInterval 13 2922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2922 : oddCount 2922 13 = 6 ∧ acceleratedOrbit 13 2922 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2922) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2922.1, data_13_2922.2]

end Collatz.Research.StoppingAtlas.Batch0657
