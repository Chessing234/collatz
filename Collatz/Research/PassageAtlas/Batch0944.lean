import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0944

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30900. -/
theorem bounds_15_30900 : exactInterval 15 30900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30900 : oddCount 30900 15 = 7 ∧ acceleratedOrbit 15 30900 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30900) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30900.1, data_15_30900.2]

/-- Complete interval computation for depth 15, residue 30901. -/
theorem bounds_15_30901 : exactInterval 15 30901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30901 : oddCount 30901 15 = 7 ∧ acceleratedOrbit 15 30901 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30901) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30901.1, data_15_30901.2]

/-- Complete interval computation for depth 15, residue 30902. -/
theorem bounds_15_30902 : exactInterval 15 30902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30902 : oddCount 30902 15 = 8 ∧ acceleratedOrbit 15 30902 = 6188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30902) = 3 ^ 8 * m + 6188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30902.1, data_15_30902.2]

/-- Complete interval computation for depth 15, residue 30903. -/
theorem bounds_15_30903 : exactInterval 15 30903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30903 : oddCount 30903 15 = 8 ∧ acceleratedOrbit 15 30903 = 6188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30903) = 3 ^ 8 * m + 6188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30903.1, data_15_30903.2]

/-- Complete interval computation for depth 15, residue 30904. -/
theorem bounds_15_30904 : exactInterval 15 30904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30904 : oddCount 30904 15 = 7 ∧ acceleratedOrbit 15 30904 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30904) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30904.1, data_15_30904.2]

/-- Complete interval computation for depth 15, residue 30905. -/
theorem bounds_15_30905 : exactInterval 15 30905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30905 : oddCount 30905 15 = 7 ∧ acceleratedOrbit 15 30905 = 2063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30905) = 3 ^ 7 * m + 2063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30905.1, data_15_30905.2]

/-- Complete interval computation for depth 15, residue 30906. -/
theorem bounds_15_30906 : exactInterval 15 30906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30906 : oddCount 30906 15 = 7 ∧ acceleratedOrbit 15 30906 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30906) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30906.1, data_15_30906.2]

/-- Complete interval computation for depth 15, residue 30907. -/
theorem bounds_15_30907 : exactInterval 15 30907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30907 : oddCount 30907 15 = 11 ∧ acceleratedOrbit 15 30907 = 167102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30907) = 3 ^ 11 * m + 167102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30907.1, data_15_30907.2]

/-- Complete interval computation for depth 15, residue 30908. -/
theorem bounds_15_30908 : exactInterval 15 30908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30908 : oddCount 30908 15 = 9 ∧ acceleratedOrbit 15 30908 = 18569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30908) = 3 ^ 9 * m + 18569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30908.1, data_15_30908.2]

/-- Complete interval computation for depth 15, residue 30909. -/
theorem bounds_15_30909 : exactInterval 15 30909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30909 : oddCount 30909 15 = 9 ∧ acceleratedOrbit 15 30909 = 18569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30909) = 3 ^ 9 * m + 18569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30909.1, data_15_30909.2]

/-- Complete interval computation for depth 15, residue 30910. -/
theorem bounds_15_30910 : exactInterval 15 30910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30910 : oddCount 30910 15 = 9 ∧ acceleratedOrbit 15 30910 = 18569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30910) = 3 ^ 9 * m + 18569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30910.1, data_15_30910.2]

/-- Complete interval computation for depth 15, residue 30911. -/
theorem bounds_15_30911 : exactInterval 15 30911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30911 : oddCount 30911 15 = 9 ∧ acceleratedOrbit 15 30911 = 18569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30911) = 3 ^ 9 * m + 18569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30911.1, data_15_30911.2]

/-- Complete interval computation for depth 15, residue 30912. -/
theorem bounds_15_30912 : exactInterval 15 30912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30912 : oddCount 30912 15 = 3 ∧ acceleratedOrbit 15 30912 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30912) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30912.1, data_15_30912.2]

/-- Complete interval computation for depth 15, residue 30913. -/
theorem bounds_15_30913 : exactInterval 15 30913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30913 : oddCount 30913 15 = 9 ∧ acceleratedOrbit 15 30913 = 18575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30913) = 3 ^ 9 * m + 18575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30913.1, data_15_30913.2]

/-- Complete interval computation for depth 15, residue 30914. -/
theorem bounds_15_30914 : exactInterval 15 30914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30914 : oddCount 30914 15 = 9 ∧ acceleratedOrbit 15 30914 = 18575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30914) = 3 ^ 9 * m + 18575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30914.1, data_15_30914.2]

/-- Complete interval computation for depth 15, residue 30915. -/
theorem bounds_15_30915 : exactInterval 15 30915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30915 : oddCount 30915 15 = 9 ∧ acceleratedOrbit 15 30915 = 18575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30915) = 3 ^ 9 * m + 18575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30915.1, data_15_30915.2]

/-- Complete interval computation for depth 15, residue 30916. -/
theorem bounds_15_30916 : exactInterval 15 30916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30916 : oddCount 30916 15 = 8 ∧ acceleratedOrbit 15 30916 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30916) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30916.1, data_15_30916.2]

/-- Complete interval computation for depth 15, residue 30917. -/
theorem bounds_15_30917 : exactInterval 15 30917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30917 : oddCount 30917 15 = 8 ∧ acceleratedOrbit 15 30917 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30917) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30917.1, data_15_30917.2]

/-- Complete interval computation for depth 15, residue 30918. -/
theorem bounds_15_30918 : exactInterval 15 30918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30918 : oddCount 30918 15 = 8 ∧ acceleratedOrbit 15 30918 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30918) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30918.1, data_15_30918.2]

/-- Complete interval computation for depth 15, residue 30919. -/
theorem bounds_15_30919 : exactInterval 15 30919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30919 : oddCount 30919 15 = 9 ∧ acceleratedOrbit 15 30919 = 18575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30919) = 3 ^ 9 * m + 18575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30919.1, data_15_30919.2]

/-- Complete interval computation for depth 15, residue 30920. -/
theorem bounds_15_30920 : exactInterval 15 30920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30920 : oddCount 30920 15 = 8 ∧ acceleratedOrbit 15 30920 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30920) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30920.1, data_15_30920.2]

/-- Complete interval computation for depth 15, residue 30921. -/
theorem bounds_15_30921 : exactInterval 15 30921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30921 : oddCount 30921 15 = 7 ∧ acceleratedOrbit 15 30921 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30921) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30921.1, data_15_30921.2]

/-- Complete interval computation for depth 15, residue 30922. -/
theorem bounds_15_30922 : exactInterval 15 30922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30922 : oddCount 30922 15 = 8 ∧ acceleratedOrbit 15 30922 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30922) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30922.1, data_15_30922.2]

/-- Complete interval computation for depth 15, residue 30923. -/
theorem bounds_15_30923 : exactInterval 15 30923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30923 : oddCount 30923 15 = 8 ∧ acceleratedOrbit 15 30923 = 6193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30923) = 3 ^ 8 * m + 6193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30923.1, data_15_30923.2]

/-- Complete interval computation for depth 15, residue 30924. -/
theorem bounds_15_30924 : exactInterval 15 30924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30924 : oddCount 30924 15 = 8 ∧ acceleratedOrbit 15 30924 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30924) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30924.1, data_15_30924.2]

/-- Complete interval computation for depth 15, residue 30925. -/
theorem bounds_15_30925 : exactInterval 15 30925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30925 : oddCount 30925 15 = 8 ∧ acceleratedOrbit 15 30925 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30925) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30925.1, data_15_30925.2]

/-- Complete interval computation for depth 15, residue 30926. -/
theorem bounds_15_30926 : exactInterval 15 30926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30926 : oddCount 30926 15 = 11 ∧ acceleratedOrbit 15 30926 = 167204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30926) = 3 ^ 11 * m + 167204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30926.1, data_15_30926.2]

/-- Complete interval computation for depth 15, residue 30927. -/
theorem bounds_15_30927 : exactInterval 15 30927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30927 : oddCount 30927 15 = 11 ∧ acceleratedOrbit 15 30927 = 167204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30927) = 3 ^ 11 * m + 167204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30927.1, data_15_30927.2]

/-- Complete interval computation for depth 15, residue 30928. -/
theorem bounds_15_30928 : exactInterval 15 30928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30928 : oddCount 30928 15 = 3 ∧ acceleratedOrbit 15 30928 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30928) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30928.1, data_15_30928.2]

/-- Complete interval computation for depth 15, residue 30929. -/
theorem bounds_15_30929 : exactInterval 15 30929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30929 : oddCount 30929 15 = 8 ∧ acceleratedOrbit 15 30929 = 6194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30929) = 3 ^ 8 * m + 6194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30929.1, data_15_30929.2]

/-- Complete interval computation for depth 15, residue 30930. -/
theorem bounds_15_30930 : exactInterval 15 30930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30930 : oddCount 30930 15 = 8 ∧ acceleratedOrbit 15 30930 = 6194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30930) = 3 ^ 8 * m + 6194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30930.1, data_15_30930.2]

/-- Complete interval computation for depth 15, residue 30931. -/
theorem bounds_15_30931 : exactInterval 15 30931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30931 : oddCount 30931 15 = 8 ∧ acceleratedOrbit 15 30931 = 6194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30931) = 3 ^ 8 * m + 6194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30931.1, data_15_30931.2]

end Collatz.Research.PassageAtlas.Batch0944
