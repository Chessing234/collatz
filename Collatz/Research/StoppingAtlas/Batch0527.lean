import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0527

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 911. -/
theorem bounds_13_911 : exactInterval 13 911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 911) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_911 : oddCount 911 13 = 7 ∧ acceleratedOrbit 13 911 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 911) = 3 ^ 7 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_911.1, data_13_911.2]

/-- Complete interval computation for depth 13, residue 912. -/
theorem bounds_13_912 : exactInterval 13 912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_912 : oddCount 912 13 = 5 ∧ acceleratedOrbit 13 912 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 912) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_912.1, data_13_912.2]

/-- Complete interval computation for depth 13, residue 913. -/
theorem bounds_13_913 : exactInterval 13 913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_913 : oddCount 913 13 = 6 ∧ acceleratedOrbit 13 913 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 913) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_913.1, data_13_913.2]

/-- Complete interval computation for depth 13, residue 914. -/
theorem bounds_13_914 : exactInterval 13 914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_914 : oddCount 914 13 = 6 ∧ acceleratedOrbit 13 914 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 914) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_914.1, data_13_914.2]

/-- Complete interval computation for depth 13, residue 915. -/
theorem bounds_13_915 : exactInterval 13 915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_915 : oddCount 915 13 = 6 ∧ acceleratedOrbit 13 915 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 915) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_915.1, data_13_915.2]

/-- Complete interval computation for depth 13, residue 916. -/
theorem bounds_13_916 : exactInterval 13 916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_916 : oddCount 916 13 = 5 ∧ acceleratedOrbit 13 916 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 916) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_916.1, data_13_916.2]

/-- Complete interval computation for depth 13, residue 917. -/
theorem bounds_13_917 : exactInterval 13 917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_917 : oddCount 917 13 = 5 ∧ acceleratedOrbit 13 917 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 917) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_917.1, data_13_917.2]

/-- Complete interval computation for depth 13, residue 918. -/
theorem bounds_13_918 : exactInterval 13 918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_918 : oddCount 918 13 = 6 ∧ acceleratedOrbit 13 918 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 918) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_918.1, data_13_918.2]

/-- Complete interval computation for depth 13, residue 919. -/
theorem bounds_13_919 : exactInterval 13 919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_919 : oddCount 919 13 = 6 ∧ acceleratedOrbit 13 919 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 919) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_919.1, data_13_919.2]

/-- Complete interval computation for depth 13, residue 920. -/
theorem bounds_13_920 : exactInterval 13 920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_920 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 920) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_920 : oddCount 920 13 = 5 ∧ acceleratedOrbit 13 920 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_920 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 920) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_920.1, data_13_920.2]

/-- Complete interval computation for depth 13, residue 921. -/
theorem bounds_13_921 : exactInterval 13 921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_921 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 921) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_921 : oddCount 921 13 = 6 ∧ acceleratedOrbit 13 921 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_921 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 921) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_921.1, data_13_921.2]

/-- Complete interval computation for depth 13, residue 922. -/
theorem bounds_13_922 : exactInterval 13 922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_922 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 922) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_922 : oddCount 922 13 = 5 ∧ acceleratedOrbit 13 922 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_922 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 922) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_922.1, data_13_922.2]

/-- Complete interval computation for depth 13, residue 923. -/
theorem bounds_13_923 : exactInterval 13 923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_923 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 923) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_923 : oddCount 923 13 = 7 ∧ acceleratedOrbit 13 923 = 247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_923 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 923) = 3 ^ 7 * m + 247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_923.1, data_13_923.2]

/-- Complete interval computation for depth 13, residue 924. -/
theorem bounds_13_924 : exactInterval 13 924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_924 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 924) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_924 : oddCount 924 13 = 7 ∧ acceleratedOrbit 13 924 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_924 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 924) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_924.1, data_13_924.2]

/-- Complete interval computation for depth 13, residue 925. -/
theorem bounds_13_925 : exactInterval 13 925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_925 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 925) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_925 : oddCount 925 13 = 7 ∧ acceleratedOrbit 13 925 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_925 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 925) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_925.1, data_13_925.2]

end Collatz.Research.StoppingAtlas.Batch0527
