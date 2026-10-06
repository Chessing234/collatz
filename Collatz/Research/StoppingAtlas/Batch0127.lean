import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0127

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 911. -/
theorem bounds_11_911 : exactInterval 11 911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_911 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 911) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_911 : oddCount 911 11 = 6 ∧ acceleratedOrbit 11 911 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_911 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 911) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_911.1, data_11_911.2]

/-- Complete interval computation for depth 11, residue 912. -/
theorem bounds_11_912 : exactInterval 11 912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_912 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 912) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_912 : oddCount 912 11 = 4 ∧ acceleratedOrbit 11 912 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_912 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 912) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_912.1, data_11_912.2]

/-- Complete interval computation for depth 11, residue 913. -/
theorem bounds_11_913 : exactInterval 11 913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_913 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 913) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_913 : oddCount 913 11 = 5 ∧ acceleratedOrbit 11 913 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_913 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 913) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_913.1, data_11_913.2]

/-- Complete interval computation for depth 11, residue 914. -/
theorem bounds_11_914 : exactInterval 11 914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_914 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 914) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_914 : oddCount 914 11 = 5 ∧ acceleratedOrbit 11 914 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_914 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 914) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_914.1, data_11_914.2]

/-- Complete interval computation for depth 11, residue 915. -/
theorem bounds_11_915 : exactInterval 11 915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_915 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 915) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_915 : oddCount 915 11 = 5 ∧ acceleratedOrbit 11 915 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_915 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 915) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_915.1, data_11_915.2]

/-- Complete interval computation for depth 11, residue 916. -/
theorem bounds_11_916 : exactInterval 11 916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_916 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 916) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_916 : oddCount 916 11 = 4 ∧ acceleratedOrbit 11 916 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_916 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 916) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_916.1, data_11_916.2]

/-- Complete interval computation for depth 11, residue 917. -/
theorem bounds_11_917 : exactInterval 11 917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_917 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 917) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_917 : oddCount 917 11 = 4 ∧ acceleratedOrbit 11 917 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_917 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 917) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_917.1, data_11_917.2]

/-- Complete interval computation for depth 11, residue 918. -/
theorem bounds_11_918 : exactInterval 11 918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_918 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 918) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_918 : oddCount 918 11 = 5 ∧ acceleratedOrbit 11 918 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_918 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 918) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_918.1, data_11_918.2]

/-- Complete interval computation for depth 11, residue 919. -/
theorem bounds_11_919 : exactInterval 11 919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_919 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 919) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_919 : oddCount 919 11 = 5 ∧ acceleratedOrbit 11 919 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_919 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 919) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_919.1, data_11_919.2]

/-- Complete interval computation for depth 11, residue 920. -/
theorem bounds_11_920 : exactInterval 11 920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_920 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 920) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_920 : oddCount 920 11 = 4 ∧ acceleratedOrbit 11 920 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_920 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 920) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_920.1, data_11_920.2]

/-- Complete interval computation for depth 11, residue 921. -/
theorem bounds_11_921 : exactInterval 11 921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_921 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 921) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_921 : oddCount 921 11 = 5 ∧ acceleratedOrbit 11 921 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_921 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 921) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_921.1, data_11_921.2]

/-- Complete interval computation for depth 11, residue 922. -/
theorem bounds_11_922 : exactInterval 11 922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_922 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 922) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_922 : oddCount 922 11 = 4 ∧ acceleratedOrbit 11 922 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_922 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 922) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_922.1, data_11_922.2]

/-- Complete interval computation for depth 11, residue 923. -/
theorem bounds_11_923 : exactInterval 11 923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_923 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 923) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_923 : oddCount 923 11 = 6 ∧ acceleratedOrbit 11 923 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_923 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 923) = 3 ^ 6 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_923.1, data_11_923.2]

/-- Complete interval computation for depth 11, residue 924. -/
theorem bounds_11_924 : exactInterval 11 924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_924 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 924) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_924 : oddCount 924 11 = 7 ∧ acceleratedOrbit 11 924 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_924 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 924) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_924.1, data_11_924.2]

/-- Complete interval computation for depth 11, residue 925. -/
theorem bounds_11_925 : exactInterval 11 925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_925 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 925) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_925 : oddCount 925 11 = 7 ∧ acceleratedOrbit 11 925 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_925 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 925) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_925.1, data_11_925.2]

end Collatz.Research.StoppingAtlas.Batch0127
