import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0883

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28901. -/
theorem bounds_15_28901 : exactInterval 15 28901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28901 : oddCount 28901 15 = 7 ∧ acceleratedOrbit 15 28901 = 1930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28901) = 3 ^ 7 * m + 1930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28901.1, data_15_28901.2]

/-- Complete interval computation for depth 15, residue 28902. -/
theorem bounds_15_28902 : exactInterval 15 28902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28902 : oddCount 28902 15 = 7 ∧ acceleratedOrbit 15 28902 = 1930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28902) = 3 ^ 7 * m + 1930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28902.1, data_15_28902.2]

/-- Complete interval computation for depth 15, residue 28903. -/
theorem bounds_15_28903 : exactInterval 15 28903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28903 : oddCount 28903 15 = 9 ∧ acceleratedOrbit 15 28903 = 17363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28903) = 3 ^ 9 * m + 17363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28903.1, data_15_28903.2]

/-- Complete interval computation for depth 15, residue 28904. -/
theorem bounds_15_28904 : exactInterval 15 28904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28904 : oddCount 28904 15 = 5 ∧ acceleratedOrbit 15 28904 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28904) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28904.1, data_15_28904.2]

/-- Complete interval computation for depth 15, residue 28905. -/
theorem bounds_15_28905 : exactInterval 15 28905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28905 : oddCount 28905 15 = 8 ∧ acceleratedOrbit 15 28905 = 5788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28905) = 3 ^ 8 * m + 5788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28905.1, data_15_28905.2]

/-- Complete interval computation for depth 15, residue 28906. -/
theorem bounds_15_28906 : exactInterval 15 28906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28906 : oddCount 28906 15 = 5 ∧ acceleratedOrbit 15 28906 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28906) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28906.1, data_15_28906.2]

/-- Complete interval computation for depth 15, residue 28907. -/
theorem bounds_15_28907 : exactInterval 15 28907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28907 : oddCount 28907 15 = 10 ∧ acceleratedOrbit 15 28907 = 52096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28907) = 3 ^ 10 * m + 52096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28907.1, data_15_28907.2]

/-- Complete interval computation for depth 15, residue 28908. -/
theorem bounds_15_28908 : exactInterval 15 28908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28908 : oddCount 28908 15 = 8 ∧ acceleratedOrbit 15 28908 = 5791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28908) = 3 ^ 8 * m + 5791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28908.1, data_15_28908.2]

/-- Complete interval computation for depth 15, residue 28909. -/
theorem bounds_15_28909 : exactInterval 15 28909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28909 : oddCount 28909 15 = 8 ∧ acceleratedOrbit 15 28909 = 5791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28909) = 3 ^ 8 * m + 5791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28909.1, data_15_28909.2]

/-- Complete interval computation for depth 15, residue 28910. -/
theorem bounds_15_28910 : exactInterval 15 28910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28910 : oddCount 28910 15 = 8 ∧ acceleratedOrbit 15 28910 = 5791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28910) = 3 ^ 8 * m + 5791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28910.1, data_15_28910.2]

/-- Complete interval computation for depth 15, residue 28911. -/
theorem bounds_15_28911 : exactInterval 15 28911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28911 : oddCount 28911 15 = 12 ∧ acceleratedOrbit 15 28911 = 468908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28911) = 3 ^ 12 * m + 468908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28911.1, data_15_28911.2]

/-- Complete interval computation for depth 15, residue 28912. -/
theorem bounds_15_28912 : exactInterval 15 28912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28912 : oddCount 28912 15 = 5 ∧ acceleratedOrbit 15 28912 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28912) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28912.1, data_15_28912.2]

/-- Complete interval computation for depth 15, residue 28913. -/
theorem bounds_15_28913 : exactInterval 15 28913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28913 : oddCount 28913 15 = 5 ∧ acceleratedOrbit 15 28913 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28913) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28913.1, data_15_28913.2]

/-- Complete interval computation for depth 15, residue 28914. -/
theorem bounds_15_28914 : exactInterval 15 28914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28914 : oddCount 28914 15 = 9 ∧ acceleratedOrbit 15 28914 = 17371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28914) = 3 ^ 9 * m + 17371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28914.1, data_15_28914.2]

/-- Complete interval computation for depth 15, residue 28915. -/
theorem bounds_15_28915 : exactInterval 15 28915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28915 : oddCount 28915 15 = 9 ∧ acceleratedOrbit 15 28915 = 17371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28915) = 3 ^ 9 * m + 17371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28915.1, data_15_28915.2]

/-- Complete interval computation for depth 15, residue 28916. -/
theorem bounds_15_28916 : exactInterval 15 28916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28916 : oddCount 28916 15 = 5 ∧ acceleratedOrbit 15 28916 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28916) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28916.1, data_15_28916.2]

/-- Complete interval computation for depth 15, residue 28917. -/
theorem bounds_15_28917 : exactInterval 15 28917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28917 : oddCount 28917 15 = 5 ∧ acceleratedOrbit 15 28917 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28917) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28917.1, data_15_28917.2]

/-- Complete interval computation for depth 15, residue 28918. -/
theorem bounds_15_28918 : exactInterval 15 28918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28918 : oddCount 28918 15 = 9 ∧ acceleratedOrbit 15 28918 = 17374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28918) = 3 ^ 9 * m + 17374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28918.1, data_15_28918.2]

/-- Complete interval computation for depth 15, residue 28919. -/
theorem bounds_15_28919 : exactInterval 15 28919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28919 : oddCount 28919 15 = 9 ∧ acceleratedOrbit 15 28919 = 17374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28919) = 3 ^ 9 * m + 17374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28919.1, data_15_28919.2]

/-- Complete interval computation for depth 15, residue 28920. -/
theorem bounds_15_28920 : exactInterval 15 28920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28920 : oddCount 28920 15 = 9 ∧ acceleratedOrbit 15 28920 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28920) = 3 ^ 9 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28920.1, data_15_28920.2]

/-- Complete interval computation for depth 15, residue 28921. -/
theorem bounds_15_28921 : exactInterval 15 28921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28921 : oddCount 28921 15 = 10 ∧ acceleratedOrbit 15 28921 = 52123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28921) = 3 ^ 10 * m + 52123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28921.1, data_15_28921.2]

/-- Complete interval computation for depth 15, residue 28922. -/
theorem bounds_15_28922 : exactInterval 15 28922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28922 : oddCount 28922 15 = 9 ∧ acceleratedOrbit 15 28922 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28922) = 3 ^ 9 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28922.1, data_15_28922.2]

/-- Complete interval computation for depth 15, residue 28923. -/
theorem bounds_15_28923 : exactInterval 15 28923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28923 : oddCount 28923 15 = 12 ∧ acceleratedOrbit 15 28923 = 469111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28923) = 3 ^ 12 * m + 469111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28923.1, data_15_28923.2]

/-- Complete interval computation for depth 15, residue 28924. -/
theorem bounds_15_28924 : exactInterval 15 28924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28924 : oddCount 28924 15 = 9 ∧ acceleratedOrbit 15 28924 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28924) = 3 ^ 9 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28924.1, data_15_28924.2]

/-- Complete interval computation for depth 15, residue 28925. -/
theorem bounds_15_28925 : exactInterval 15 28925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28925 : oddCount 28925 15 = 9 ∧ acceleratedOrbit 15 28925 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28925) = 3 ^ 9 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28925.1, data_15_28925.2]

/-- Complete interval computation for depth 15, residue 28926. -/
theorem bounds_15_28926 : exactInterval 15 28926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28926 : oddCount 28926 15 = 10 ∧ acceleratedOrbit 15 28926 = 52130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28926) = 3 ^ 10 * m + 52130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28926.1, data_15_28926.2]

/-- Complete interval computation for depth 15, residue 28927. -/
theorem bounds_15_28927 : exactInterval 15 28927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28927 : oddCount 28927 15 = 10 ∧ acceleratedOrbit 15 28927 = 52130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28927) = 3 ^ 10 * m + 52130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28927.1, data_15_28927.2]

/-- Complete interval computation for depth 15, residue 28928. -/
theorem bounds_15_28928 : exactInterval 15 28928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28928 : oddCount 28928 15 = 2 ∧ acceleratedOrbit 15 28928 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28928) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28928.1, data_15_28928.2]

/-- Complete interval computation for depth 15, residue 28929. -/
theorem bounds_15_28929 : exactInterval 15 28929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28929 : oddCount 28929 15 = 8 ∧ acceleratedOrbit 15 28929 = 5795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28929) = 3 ^ 8 * m + 5795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28929.1, data_15_28929.2]

/-- Complete interval computation for depth 15, residue 28930. -/
theorem bounds_15_28930 : exactInterval 15 28930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28930 : oddCount 28930 15 = 8 ∧ acceleratedOrbit 15 28930 = 5795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28930) = 3 ^ 8 * m + 5795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28930.1, data_15_28930.2]

/-- Complete interval computation for depth 15, residue 28931. -/
theorem bounds_15_28931 : exactInterval 15 28931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28931 : oddCount 28931 15 = 8 ∧ acceleratedOrbit 15 28931 = 5795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28931) = 3 ^ 8 * m + 5795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28931.1, data_15_28931.2]

/-- Complete interval computation for depth 15, residue 28932. -/
theorem bounds_15_28932 : exactInterval 15 28932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28932 : oddCount 28932 15 = 7 ∧ acceleratedOrbit 15 28932 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28932) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28932.1, data_15_28932.2]

/-- Complete interval computation for depth 15, residue 28933. -/
theorem bounds_15_28933 : exactInterval 15 28933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28933 : oddCount 28933 15 = 7 ∧ acceleratedOrbit 15 28933 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28933) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28933.1, data_15_28933.2]

end Collatz.Research.PassageAtlas.Batch0883
