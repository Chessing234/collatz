import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0260

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 906. -/
theorem bounds_12_906 : exactInterval 12 906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_906 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 906) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_906 : oddCount 906 12 = 2 ∧ acceleratedOrbit 12 906 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_906 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 906) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_906.1, data_12_906.2]

/-- Complete interval computation for depth 12, residue 907. -/
theorem bounds_12_907 : exactInterval 12 907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_907 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 907) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_907 : oddCount 907 12 = 9 ∧ acceleratedOrbit 12 907 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_907 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 907) = 3 ^ 9 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_907.1, data_12_907.2]

/-- Complete interval computation for depth 12, residue 908. -/
theorem bounds_12_908 : exactInterval 12 908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_908 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 908) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_908 : oddCount 908 12 = 2 ∧ acceleratedOrbit 12 908 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_908 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 908) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_908.1, data_12_908.2]

/-- Complete interval computation for depth 12, residue 909. -/
theorem bounds_12_909 : exactInterval 12 909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_909 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 909) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_909 : oddCount 909 12 = 2 ∧ acceleratedOrbit 12 909 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_909 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 909) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_909.1, data_12_909.2]

/-- Complete interval computation for depth 12, residue 910. -/
theorem bounds_12_910 : exactInterval 12 910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_910 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 910) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_910 : oddCount 910 12 = 7 ∧ acceleratedOrbit 12 910 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_910 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 910) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_910.1, data_12_910.2]

/-- Complete interval computation for depth 12, residue 911. -/
theorem bounds_12_911 : exactInterval 12 911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_911 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 911) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_911 : oddCount 911 12 = 7 ∧ acceleratedOrbit 12 911 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_911 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 911) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_911.1, data_12_911.2]

/-- Complete interval computation for depth 12, residue 912. -/
theorem bounds_12_912 : exactInterval 12 912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_912 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 912) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_912 : oddCount 912 12 = 5 ∧ acceleratedOrbit 12 912 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_912 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 912) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_912.1, data_12_912.2]

/-- Complete interval computation for depth 12, residue 913. -/
theorem bounds_12_913 : exactInterval 12 913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_913 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 913) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_913 : oddCount 913 12 = 6 ∧ acceleratedOrbit 12 913 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_913 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 913) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_913.1, data_12_913.2]

/-- Complete interval computation for depth 12, residue 914. -/
theorem bounds_12_914 : exactInterval 12 914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_914 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 914) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_914 : oddCount 914 12 = 6 ∧ acceleratedOrbit 12 914 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_914 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 914) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_914.1, data_12_914.2]

/-- Complete interval computation for depth 12, residue 915. -/
theorem bounds_12_915 : exactInterval 12 915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_915 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 915) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_915 : oddCount 915 12 = 6 ∧ acceleratedOrbit 12 915 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_915 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 915) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_915.1, data_12_915.2]

/-- Complete interval computation for depth 12, residue 916. -/
theorem bounds_12_916 : exactInterval 12 916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_916 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 916) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_916 : oddCount 916 12 = 5 ∧ acceleratedOrbit 12 916 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_916 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 916) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_916.1, data_12_916.2]

/-- Complete interval computation for depth 12, residue 917. -/
theorem bounds_12_917 : exactInterval 12 917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_917 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 917) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_917 : oddCount 917 12 = 5 ∧ acceleratedOrbit 12 917 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_917 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 917) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_917.1, data_12_917.2]

/-- Complete interval computation for depth 12, residue 918. -/
theorem bounds_12_918 : exactInterval 12 918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_918 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 918) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_918 : oddCount 918 12 = 5 ∧ acceleratedOrbit 12 918 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_918 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 918) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_918.1, data_12_918.2]

/-- Complete interval computation for depth 12, residue 919. -/
theorem bounds_12_919 : exactInterval 12 919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_919 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 919) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_919 : oddCount 919 12 = 5 ∧ acceleratedOrbit 12 919 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_919 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 919) = 3 ^ 5 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_919.1, data_12_919.2]

/-- Complete interval computation for depth 12, residue 920. -/
theorem bounds_12_920 : exactInterval 12 920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_920 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 920) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_920 : oddCount 920 12 = 5 ∧ acceleratedOrbit 12 920 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_920 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 920) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_920.1, data_12_920.2]

end Collatz.Research.StoppingAtlas.Batch0260
