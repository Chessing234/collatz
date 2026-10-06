import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0060

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 906. -/
theorem bounds_10_906 : exactInterval 10 906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_906 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 906) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_906 : oddCount 906 10 = 2 ∧ acceleratedOrbit 10 906 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_906 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 906) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_906.1, data_10_906.2]

/-- Complete interval computation for depth 10, residue 907. -/
theorem bounds_10_907 : exactInterval 10 907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_907 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 907) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_907 : oddCount 907 10 = 7 ∧ acceleratedOrbit 10 907 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_907 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 907) = 3 ^ 7 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_907.1, data_10_907.2]

/-- Complete interval computation for depth 10, residue 908. -/
theorem bounds_10_908 : exactInterval 10 908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_908 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 908) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_908 : oddCount 908 10 = 2 ∧ acceleratedOrbit 10 908 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_908 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 908) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_908.1, data_10_908.2]

/-- Complete interval computation for depth 10, residue 909. -/
theorem bounds_10_909 : exactInterval 10 909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_909 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 909) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_909 : oddCount 909 10 = 2 ∧ acceleratedOrbit 10 909 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_909 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 909) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_909.1, data_10_909.2]

/-- Complete interval computation for depth 10, residue 910. -/
theorem bounds_10_910 : exactInterval 10 910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_910 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 910) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_910 : oddCount 910 10 = 6 ∧ acceleratedOrbit 10 910 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_910 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 910) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_910.1, data_10_910.2]

/-- Complete interval computation for depth 10, residue 911. -/
theorem bounds_10_911 : exactInterval 10 911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_911 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 911) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_911 : oddCount 911 10 = 6 ∧ acceleratedOrbit 10 911 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_911 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 911) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_911.1, data_10_911.2]

/-- Complete interval computation for depth 10, residue 912. -/
theorem bounds_10_912 : exactInterval 10 912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_912 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 912) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_912 : oddCount 912 10 = 4 ∧ acceleratedOrbit 10 912 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_912 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 912) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_912.1, data_10_912.2]

/-- Complete interval computation for depth 10, residue 913. -/
theorem bounds_10_913 : exactInterval 10 913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_913 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 913) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_913 : oddCount 913 10 = 5 ∧ acceleratedOrbit 10 913 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_913 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 913) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_913.1, data_10_913.2]

/-- Complete interval computation for depth 10, residue 914. -/
theorem bounds_10_914 : exactInterval 10 914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_914 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 914) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_914 : oddCount 914 10 = 5 ∧ acceleratedOrbit 10 914 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_914 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 914) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_914.1, data_10_914.2]

/-- Complete interval computation for depth 10, residue 915. -/
theorem bounds_10_915 : exactInterval 10 915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_915 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 915) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_915 : oddCount 915 10 = 5 ∧ acceleratedOrbit 10 915 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_915 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 915) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_915.1, data_10_915.2]

/-- Complete interval computation for depth 10, residue 916. -/
theorem bounds_10_916 : exactInterval 10 916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_916 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 916) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_916 : oddCount 916 10 = 4 ∧ acceleratedOrbit 10 916 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_916 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 916) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_916.1, data_10_916.2]

/-- Complete interval computation for depth 10, residue 917. -/
theorem bounds_10_917 : exactInterval 10 917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_917 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 917) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_917 : oddCount 917 10 = 4 ∧ acceleratedOrbit 10 917 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_917 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 917) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_917.1, data_10_917.2]

/-- Complete interval computation for depth 10, residue 918. -/
theorem bounds_10_918 : exactInterval 10 918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_918 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 918) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_918 : oddCount 918 10 = 4 ∧ acceleratedOrbit 10 918 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_918 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 918) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_918.1, data_10_918.2]

/-- Complete interval computation for depth 10, residue 919. -/
theorem bounds_10_919 : exactInterval 10 919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_919 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 919) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_919 : oddCount 919 10 = 4 ∧ acceleratedOrbit 10 919 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_919 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 919) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_919.1, data_10_919.2]

/-- Complete interval computation for depth 10, residue 920. -/
theorem bounds_10_920 : exactInterval 10 920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_920 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 920) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_920 : oddCount 920 10 = 4 ∧ acceleratedOrbit 10 920 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_920 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 920) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_920.1, data_10_920.2]

end Collatz.Research.StoppingAtlas.Batch0060
